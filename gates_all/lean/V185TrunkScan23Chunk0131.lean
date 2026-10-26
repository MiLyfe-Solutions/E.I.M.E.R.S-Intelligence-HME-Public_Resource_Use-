import V185TrunkScan23Chunk0130

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_776043 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 3]
def baseStart_776043 : Nat := 118140960795 + 776043 * 2 ^ 59
def prefixEnd_776043 : Nat := 4983230072969 + 3 ^ 40 * 776043 * 2
def baseEnd_776043 : Nat := 398483067557212461893549

theorem tailTrace_776043 : CollatzResearch.WordTrace tailWord_776043 prefixEnd_776043 398483067557212461893549 := by
  unfold tailWord_776043
  simp only [CollatzResearch.WordTrace]
  refine ⟨28304613527536223437652783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18869742351690815625101855 28304613527536223437652783)
  ·
    refine ⟨42456920291304335156479175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28304613527536223437652783 42456920291304335156479175)
    ·
      refine ⟨63685380436956502734718763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42456920291304335156479175 63685380436956502734718763)
      ·
        refine ⟨95528070655434754102078145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63685380436956502734718763 95528070655434754102078145)
        ·
          refine ⟨71646052991576065576558609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95528070655434754102078145 71646052991576065576558609)
          ·
            refine ⟨53734539743682049182418957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71646052991576065576558609 53734539743682049182418957)
            ·
              refine ⟨20150452403880768443407109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53734539743682049182418957 20150452403880768443407109)
              ·
                refine ⟨3778209825727644083138833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20150452403880768443407109 3778209825727644083138833)
                ·
                  refine ⟨2833657369295733062354125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3778209825727644083138833 2833657369295733062354125)
                  ·
                    refine ⟨1062621513485899898382797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2833657369295733062354125 1062621513485899898382797)
                    ·
                      refine ⟨398483067557212461893549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1062621513485899898382797 398483067557212461893549)
                      ·
                        rfl

theorem cell23_776043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 3].length) (baseStart_776043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776043 prefixEnd_776043 := by exact prefixLift 776043
  have htrace : WordTrace (prefixWord ++ tailWord_776043) baseStart_776043 baseEnd_776043 := by
    simpa [prefixWord, tailWord_776043, baseEnd_776043] using wordTrace_append hprefix tailTrace_776043
  have hstable : (prefixWord ++ tailWord_776043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776043).length < 2 ^ (prefixWord ++ tailWord_776043).sum := by decide
  have hdescent : baseEnd_776043 < baseStart_776043 := by decide
  rcases family_descends (prefixWord ++ tailWord_776043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776044 : List Nat := [2, 2, 1, 1, 4, 3, 2, 2, 2, 2, 2]
def baseStart_776044 : Nat := 118140960795 + 776044 * 2 ^ 59
def prefixEnd_776044 : Nat := 4983230072969 + 3 ^ 40 * 776044 * 2
def baseEnd_776044 : Nat := 398483581037866957981045

theorem tailTrace_776044 : CollatzResearch.WordTrace tailWord_776044 prefixEnd_776044 398483581037866957981045 := by
  unfold tailWord_776044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14152325000266300304219593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18869766667021733738959457 14152325000266300304219593)
  ·
    refine ⟨10614243750199725228164695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14152325000266300304219593 10614243750199725228164695)
    ·
      refine ⟨15921365625299587842247043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10614243750199725228164695 15921365625299587842247043)
      ·
        refine ⟨23882048437949381763370565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15921365625299587842247043 23882048437949381763370565)
        ·
          refine ⟨4477884082115509080631981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23882048437949381763370565 4477884082115509080631981)
          ·
            refine ⟨1679206530793315905236993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4477884082115509080631981 1679206530793315905236993)
            ·
              refine ⟨1259404898094986928927745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679206530793315905236993 1259404898094986928927745)
              ·
                refine ⟨944553673571240196695809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259404898094986928927745 944553673571240196695809)
                ·
                  refine ⟨708415255178430147521857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 944553673571240196695809 708415255178430147521857)
                  ·
                    refine ⟨531311441383822610641393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 708415255178430147521857 531311441383822610641393)
                    ·
                      refine ⟨398483581037866957981045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531311441383822610641393 398483581037866957981045)
                      ·
                        rfl

theorem cell23_776044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_776044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776044 prefixEnd_776044 := by exact prefixLift 776044
  have htrace : WordTrace (prefixWord ++ tailWord_776044) baseStart_776044 baseEnd_776044 := by
    simpa [prefixWord, tailWord_776044, baseEnd_776044] using wordTrace_append hprefix tailTrace_776044
  have hstable : (prefixWord ++ tailWord_776044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776044).length < 2 ^ (prefixWord ++ tailWord_776044).sum := by decide
  have hdescent : baseEnd_776044 < baseStart_776044 := by decide
  rcases family_descends (prefixWord ++ tailWord_776044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776117 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_776117 : Nat := 118140960795 + 776117 * 2 ^ 59
def prefixEnd_776117 : Nat := 4983230072969 + 3 ^ 40 * 776117 * 2
def baseEnd_776117 : Nat := 398521065125645172368209

theorem tailTrace_776117 : CollatzResearch.WordTrace tailWord_776117 prefixEnd_776117 398521065125645172368209 := by
  unfold tailWord_776117
  simp only [CollatzResearch.WordTrace]
  refine ⟨28307312529268134075846605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18871541686178756050564403 28307312529268134075846605)
  ·
    refine ⟨10615242198475550278442477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28307312529268134075846605 10615242198475550278442477)
    ·
      refine ⟨3980715824428331354415929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10615242198475550278442477 3980715824428331354415929)
      ·
        refine ⟨2985536868321248515811947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3980715824428331354415929 2985536868321248515811947)
        ·
          refine ⟨4478305302481872773717921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2985536868321248515811947 4478305302481872773717921)
          ·
            refine ⟨3358728976861404580288441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4478305302481872773717921 3358728976861404580288441)
            ·
              refine ⟨2519046732646053435216331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3358728976861404580288441 2519046732646053435216331)
              ·
                refine ⟨3778570098969080152824497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2519046732646053435216331 3778570098969080152824497)
                ·
                  refine ⟨2833927574226810114618373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3778570098969080152824497 2833927574226810114618373)
                  ·
                    refine ⟨531361420167526896490945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833927574226810114618373 531361420167526896490945)
                    ·
                      refine ⟨398521065125645172368209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531361420167526896490945 398521065125645172368209)
                      ·
                        rfl

theorem cell23_776117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_776117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776117 prefixEnd_776117 := by exact prefixLift 776117
  have htrace : WordTrace (prefixWord ++ tailWord_776117) baseStart_776117 baseEnd_776117 := by
    simpa [prefixWord, tailWord_776117, baseEnd_776117] using wordTrace_append hprefix tailTrace_776117
  have hstable : (prefixWord ++ tailWord_776117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776117).length < 2 ^ (prefixWord ++ tailWord_776117).sum := by decide
  have hdescent : baseEnd_776117 < baseStart_776117 := by decide
  rcases family_descends (prefixWord ++ tailWord_776117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776170 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_776170 : Nat := 118140960795 + 776170 * 2 ^ 59
def prefixEnd_776170 : Nat := 4983230072969 + 3 ^ 40 * 776170 * 2
def baseEnd_776170 : Nat := 132849426533444488335155

theorem tailTrace_776170 : CollatzResearch.WordTrace tailWord_776170 prefixEnd_776170 132849426533444488335155 := by
  unfold tailWord_776170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7077311399519031031881491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18872830398717416085017309 7077311399519031031881491)
  ·
    refine ⟨10615967099278546547822237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7077311399519031031881491 10615967099278546547822237)
    ·
      refine ⟨3980987662229454955433339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10615967099278546547822237 3980987662229454955433339)
      ·
        refine ⟨5971481493344182433150009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980987662229454955433339 5971481493344182433150009)
        ·
          refine ⟨4478611120008136824862507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5971481493344182433150009 4478611120008136824862507)
          ·
            refine ⟨6717916680012205237293761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478611120008136824862507 6717916680012205237293761)
            ·
              refine ⟨5038437510009153927970321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6717916680012205237293761 5038437510009153927970321)
              ·
                refine ⟨3778828132506865445977741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5038437510009153927970321 3778828132506865445977741)
                ·
                  refine ⟨1417060549690074542241653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3778828132506865445977741 1417060549690074542241653)
                  ·
                    refine ⟨132849426533444488335155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1417060549690074542241653 132849426533444488335155)
                    ·
                      rfl

theorem cell23_776170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_776170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776170 prefixEnd_776170 := by exact prefixLift 776170
  have htrace : WordTrace (prefixWord ++ tailWord_776170) baseStart_776170 baseEnd_776170 := by
    simpa [prefixWord, tailWord_776170, baseEnd_776170] using wordTrace_append hprefix tailTrace_776170
  have hstable : (prefixWord ++ tailWord_776170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776170).length < 2 ^ (prefixWord ++ tailWord_776170).sum := by decide
  have hdescent : baseEnd_776170 < baseStart_776170 := by decide
  rcases family_descends (prefixWord ++ tailWord_776170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776174 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_776174 : Nat := 118140960795 + 776174 * 2 ^ 59
def prefixEnd_776174 : Nat := 4983230072969 + 3 ^ 40 * 776174 * 2
def baseEnd_776174 : Nat := 44283370391439049928383

theorem tailTrace_776174 : CollatzResearch.WordTrace tailWord_776174 prefixEnd_776174 44283370391439049928383 := by
  unfold tailWord_776174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538673936257704101333947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18872927660041088540447717 3538673936257704101333947)
  ·
    refine ⟨5308010904386556152000921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3538673936257704101333947 5308010904386556152000921)
    ·
      refine ⟨3981008178289917114000691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5308010904386556152000921 3981008178289917114000691)
      ·
        refine ⟨5971512267434875671001037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981008178289917114000691 5971512267434875671001037)
        ·
          refine ⟨2239317100288078376625389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5971512267434875671001037 2239317100288078376625389)
          ·
            refine ⟨839743912608029391234521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2239317100288078376625389 839743912608029391234521)
            ·
              refine ⟨629807934456022043425891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839743912608029391234521 629807934456022043425891)
              ·
                refine ⟨944711901684033065138837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629807934456022043425891 944711901684033065138837)
                ·
                  refine ⟨44283370391439049928383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 944711901684033065138837 44283370391439049928383)
                  ·
                    rfl

theorem cell23_776174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_776174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776174 prefixEnd_776174 := by exact prefixLift 776174
  have htrace : WordTrace (prefixWord ++ tailWord_776174) baseStart_776174 baseEnd_776174 := by
    simpa [prefixWord, tailWord_776174, baseEnd_776174] using wordTrace_append hprefix tailTrace_776174
  have hstable : (prefixWord ++ tailWord_776174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776174).length < 2 ^ (prefixWord ++ tailWord_776174).sum := by decide
  have hdescent : baseEnd_776174 < baseStart_776174 := by decide
  rcases family_descends (prefixWord ++ tailWord_776174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776183 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 7, 6]
def baseStart_776183 : Nat := 118140960795 + 776183 * 2 ^ 59
def prefixEnd_776183 : Nat := 4983230072969 + 3 ^ 40 * 776183 * 2
def baseEnd_776183 : Nat := 132851651616280638047635

theorem tailTrace_776183 : CollatzResearch.WordTrace tailWord_776183 prefixEnd_776183 132851651616280638047635 := by
  unfold tailWord_776183
  simp only [CollatzResearch.WordTrace]
  refine ⟨28309719747029027347749203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18873146498019351565166135 28309719747029027347749203)
  ·
    refine ⟨42464579620543541021623805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28309719747029027347749203 42464579620543541021623805)
    ·
      refine ⟨15924217357703827883108927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42464579620543541021623805 15924217357703827883108927)
      ·
        refine ⟨23886326036555741824663391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15924217357703827883108927 23886326036555741824663391)
        ·
          refine ⟨35829489054833612736995087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23886326036555741824663391 35829489054833612736995087)
          ·
            refine ⟨53744233582250419105492631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35829489054833612736995087 53744233582250419105492631)
            ·
              refine ⟨80616350373375628658238947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53744233582250419105492631 80616350373375628658238947)
              ·
                refine ⟨120924525560063442987358421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80616350373375628658238947 120924525560063442987358421)
                ·
                  refine ⟨2834168567813986945016213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 120924525560063442987358421 2834168567813986945016213)
                  ·
                    refine ⟨132851651616280638047635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2834168567813986945016213 132851651616280638047635)
                    ·
                      rfl

theorem cell23_776183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_776183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776183 prefixEnd_776183 := by exact prefixLift 776183
  have htrace : WordTrace (prefixWord ++ tailWord_776183) baseStart_776183 baseEnd_776183 := by
    simpa [prefixWord, tailWord_776183, baseEnd_776183] using wordTrace_append hprefix tailTrace_776183
  have hstable : (prefixWord ++ tailWord_776183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776183).length < 2 ^ (prefixWord ++ tailWord_776183).sum := by decide
  have hdescent : baseEnd_776183 < baseStart_776183 := by decide
  rcases family_descends (prefixWord ++ tailWord_776183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776200 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 1, 6]
def baseStart_776200 : Nat := 118140960795 + 776200 * 2 ^ 59
def prefixEnd_776200 : Nat := 4983230072969 + 3 ^ 40 * 776200 * 2
def baseEnd_776200 : Nat := 132854561339989449210109

theorem tailTrace_776200 : CollatzResearch.WordTrace tailWord_776200 prefixEnd_776200 132854561339989449210109 := by
  unfold tailWord_776200
  simp only [CollatzResearch.WordTrace]
  refine ⟨14155169893983719625559027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18873559858644959500745369 14155169893983719625559027)
  ·
    refine ⟨21232754840975579438338541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14155169893983719625559027 21232754840975579438338541)
    ·
      refine ⟨7962283065365842289376953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21232754840975579438338541 7962283065365842289376953)
      ·
        refine ⟨5971712299024381717032715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7962283065365842289376953 5971712299024381717032715)
        ·
          refine ⟨8957568448536572575549073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5971712299024381717032715 8957568448536572575549073)
          ·
            refine ⟨6718176336402429431661805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8957568448536572575549073 6718176336402429431661805)
            ·
              refine ⟨2519316126150911036873177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6718176336402429431661805 2519316126150911036873177)
              ·
                refine ⟨1889487094613183277654883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2519316126150911036873177 1889487094613183277654883)
                ·
                  refine ⟨2834230641919774916482325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889487094613183277654883 2834230641919774916482325)
                  ·
                    refine ⟨132854561339989449210109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2834230641919774916482325 132854561339989449210109)
                    ·
                      rfl

theorem cell23_776200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_776200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776200 prefixEnd_776200 := by exact prefixLift 776200
  have htrace : WordTrace (prefixWord ++ tailWord_776200) baseStart_776200 baseEnd_776200 := by
    simpa [prefixWord, tailWord_776200, baseEnd_776200] using wordTrace_append hprefix tailTrace_776200
  have hstable : (prefixWord ++ tailWord_776200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776200).length < 2 ^ (prefixWord ++ tailWord_776200).sum := by decide
  have hdescent : baseEnd_776200 < baseStart_776200 := by decide
  rcases family_descends (prefixWord ++ tailWord_776200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776212 : List Nat := [2, 4, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_776212 : Nat := 118140960795 + 776212 * 2 ^ 59
def prefixEnd_776212 : Nat := 4983230072969 + 3 ^ 40 * 776212 * 2
def baseEnd_776212 : Nat := 132856615262607433560091

theorem tailTrace_776212 : CollatzResearch.WordTrace tailWord_776212 prefixEnd_776212 132856615262607433560091 := by
  unfold tailWord_776212
  simp only [CollatzResearch.WordTrace]
  refine ⟨14155388731961982650277445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18873851642615976867036593 14155388731961982650277445)
  ·
    refine ⟨2654135387242871746927021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14155388731961982650277445 2654135387242871746927021)
    ·
      refine ⟨995300770216076905097633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2654135387242871746927021 995300770216076905097633)
      ·
        refine ⟨746475577662057678823225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 995300770216076905097633 746475577662057678823225)
        ·
          refine ⟨559856683246543259117419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746475577662057678823225 559856683246543259117419)
          ·
            refine ⟨839785024869814888676129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559856683246543259117419 839785024869814888676129)
            ·
              refine ⟨629838768652361166507097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839785024869814888676129 629838768652361166507097)
              ·
                refine ⟨472379076489270874880323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629838768652361166507097 472379076489270874880323)
                ·
                  refine ⟨708568614733906312320485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472379076489270874880323 708568614733906312320485)
                  ·
                    refine ⟨132856615262607433560091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 708568614733906312320485 132856615262607433560091)
                    ·
                      rfl

theorem cell23_776212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_776212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776212 prefixEnd_776212 := by exact prefixLift 776212
  have htrace : WordTrace (prefixWord ++ tailWord_776212) baseStart_776212 baseEnd_776212 := by
    simpa [prefixWord, tailWord_776212, baseEnd_776212] using wordTrace_append hprefix tailTrace_776212
  have hstable : (prefixWord ++ tailWord_776212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776212).length < 2 ^ (prefixWord ++ tailWord_776212).sum := by decide
  have hdescent : baseEnd_776212 < baseStart_776212 := by decide
  rcases family_descends (prefixWord ++ tailWord_776212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776213 : List Nat := [1, 3, 2, 1, 16]
def baseStart_776213 : Nat := 118140960795 + 776213 * 2 ^ 59
def prefixEnd_776213 : Nat := 4983230072969 + 3 ^ 40 * 776213 * 2
def baseEnd_776213 : Nat := 546735746595990119023

theorem tailTrace_776213 : CollatzResearch.WordTrace tailWord_776213 prefixEnd_776213 546735746595990119023 := by
  unfold tailWord_776213
  simp only [CollatzResearch.WordTrace]
  refine ⟨28310813936920342471341293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18873875957946894980894195 28310813936920342471341293)
  ·
    refine ⟨10616555226345128426752985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28310813936920342471341293 10616555226345128426752985)
    ·
      refine ⟨7962416419758846320064739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10616555226345128426752985 7962416419758846320064739)
      ·
        refine ⟨11943624629638269480097109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7962416419758846320064739 11943624629638269480097109)
        ·
          refine ⟨546735746595990119023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 11943624629638269480097109 546735746595990119023)
          ·
            rfl

theorem cell23_776213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 16].length) (baseStart_776213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776213 prefixEnd_776213 := by exact prefixLift 776213
  have htrace : WordTrace (prefixWord ++ tailWord_776213) baseStart_776213 baseEnd_776213 := by
    simpa [prefixWord, tailWord_776213, baseEnd_776213] using wordTrace_append hprefix tailTrace_776213
  have hstable : (prefixWord ++ tailWord_776213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776213).length < 2 ^ (prefixWord ++ tailWord_776213).sum := by decide
  have hdescent : baseEnd_776213 < baseStart_776213 := by decide
  rcases family_descends (prefixWord ++ tailWord_776213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776218 : List Nat := [3, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3]
def baseStart_776218 : Nat := 118140960795 + 776218 * 2 ^ 59
def prefixEnd_776218 : Nat := 4983230072969 + 3 ^ 40 * 776218 * 2
def baseEnd_776218 : Nat := 398572926671749277205245

theorem tailTrace_776218 : CollatzResearch.WordTrace tailWord_776218 prefixEnd_776218 398572926671749277205245 := by
  unfold tailWord_776218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7077749075475557081318327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18873997534601485550182205 7077749075475557081318327)
  ·
    refine ⟨10616623613213335621977491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7077749075475557081318327 10616623613213335621977491)
    ·
      refine ⟨15924935419820003432966237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10616623613213335621977491 15924935419820003432966237)
      ·
        refine ⟨5971850782432501287362339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15924935419820003432966237 5971850782432501287362339)
        ·
          refine ⟨8957776173648751931043509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5971850782432501287362339 8957776173648751931043509)
          ·
            refine ⟨839791516279570493535329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8957776173648751931043509 839791516279570493535329)
            ·
              refine ⟨629843637209677870151497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839791516279570493535329 629843637209677870151497)
              ·
                refine ⟨472382727907258402613623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629843637209677870151497 472382727907258402613623)
                ·
                  refine ⟨708574091860887603920435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472382727907258402613623 708574091860887603920435)
                  ·
                    refine ⟨1062861137791331405880653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 708574091860887603920435 1062861137791331405880653)
                    ·
                      refine ⟨398572926671749277205245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1062861137791331405880653 398572926671749277205245)
                      ·
                        rfl

theorem cell23_776218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_776218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776218 prefixEnd_776218 := by exact prefixLift 776218
  have htrace : WordTrace (prefixWord ++ tailWord_776218) baseStart_776218 baseEnd_776218 := by
    simpa [prefixWord, tailWord_776218, baseEnd_776218] using wordTrace_append hprefix tailTrace_776218
  have hstable : (prefixWord ++ tailWord_776218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776218).length < 2 ^ (prefixWord ++ tailWord_776218).sum := by decide
  have hdescent : baseEnd_776218 < baseStart_776218 := by decide
  rcases family_descends (prefixWord ++ tailWord_776218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776234 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 2, 4]
def baseStart_776234 : Nat := 118140960795 + 776234 * 2 ^ 59
def prefixEnd_776234 : Nat := 4983230072969 + 3 ^ 40 * 776234 * 2
def baseEnd_776234 : Nat := 132860380787407071535057

theorem tailTrace_776234 : CollatzResearch.WordTrace tailWord_776234 prefixEnd_776234 132860380787407071535057 := by
  unfold tailWord_776234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7077894967461065764463939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18874386579896175371903837 7077894967461065764463939)
  ·
    refine ⟨10616842451191598646695909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7077894967461065764463939 10616842451191598646695909)
    ·
      refine ⟨1990657959598424746255483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10616842451191598646695909 1990657959598424746255483)
      ·
        refine ⟨2985986939397637119383225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1990657959598424746255483 2985986939397637119383225)
        ·
          refine ⟨2239490204548227839537419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2985986939397637119383225 2239490204548227839537419)
          ·
            refine ⟨3359235306822341759306129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2239490204548227839537419 3359235306822341759306129)
            ·
              refine ⟨2519426480116756319479597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3359235306822341759306129 2519426480116756319479597)
              ·
                refine ⟨944784930043783619804849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2519426480116756319479597 944784930043783619804849)
                ·
                  refine ⟨708588697532837714853637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 944784930043783619804849 708588697532837714853637)
                  ·
                    refine ⟨132860380787407071535057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 708588697532837714853637 132860380787407071535057)
                    ·
                      rfl

theorem cell23_776234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_776234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776234 prefixEnd_776234 := by exact prefixLift 776234
  have htrace : WordTrace (prefixWord ++ tailWord_776234) baseStart_776234 baseEnd_776234 := by
    simpa [prefixWord, tailWord_776234, baseEnd_776234] using wordTrace_append hprefix tailTrace_776234
  have hstable : (prefixWord ++ tailWord_776234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776234).length < 2 ^ (prefixWord ++ tailWord_776234).sum := by decide
  have hdescent : baseEnd_776234 < baseStart_776234 := by decide
  rcases family_descends (prefixWord ++ tailWord_776234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776301 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_776301 : Nat := 118140960795 + 776301 * 2 ^ 59
def prefixEnd_776301 : Nat := 4983230072969 + 3 ^ 40 * 776301 * 2
def baseEnd_776301 : Nat := 398615545566072452467363

theorem tailTrace_776301 : CollatzResearch.WordTrace tailWord_776301 prefixEnd_776301 398615545566072452467363 := by
  unfold tailWord_776301
  simp only [CollatzResearch.WordTrace]
  refine ⟨28314023560601533500544757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18876015707067689000363171 28314023560601533500544757)
  ·
    refine ⟨2654439708806393765676071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28314023560601533500544757 2654439708806393765676071)
    ·
      refine ⟨3981659563209590648514107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2654439708806393765676071 3981659563209590648514107)
      ·
        refine ⟨5972489344814385972771161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981659563209590648514107 5972489344814385972771161)
        ·
          refine ⟨4479367008610789479578371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5972489344814385972771161 4479367008610789479578371)
          ·
            refine ⟨6719050512916184219367557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4479367008610789479578371 6719050512916184219367557)
            ·
              refine ⟨1259821971171784541131417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6719050512916184219367557 1259821971171784541131417)
              ·
                refine ⟨944866478378838405848563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259821971171784541131417 944866478378838405848563)
                ·
                  refine ⟨1417299717568257608772845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944866478378838405848563 1417299717568257608772845)
                  ·
                    refine ⟨531487394088096603289817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417299717568257608772845 531487394088096603289817)
                    ·
                      refine ⟨398615545566072452467363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531487394088096603289817 398615545566072452467363)
                      ·
                        rfl

theorem cell23_776301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_776301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776301 prefixEnd_776301 := by exact prefixLift 776301
  have htrace : WordTrace (prefixWord ++ tailWord_776301) baseStart_776301 baseEnd_776301 := by
    simpa [prefixWord, tailWord_776301, baseEnd_776301] using wordTrace_append hprefix tailTrace_776301
  have hstable : (prefixWord ++ tailWord_776301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776301).length < 2 ^ (prefixWord ++ tailWord_776301).sum := by decide
  have hdescent : baseEnd_776301 < baseStart_776301 := by decide
  rcases family_descends (prefixWord ++ tailWord_776301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776317 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_776317 : Nat := 118140960795 + 776317 * 2 ^ 59
def prefixEnd_776317 : Nat := 4983230072969 + 3 ^ 40 * 776317 * 2
def baseEnd_776317 : Nat := 398623761256544389867289

theorem tailTrace_776317 : CollatzResearch.WordTrace tailWord_776317 prefixEnd_776317 398623761256544389867289 := by
  unfold tailWord_776317
  simp only [CollatzResearch.WordTrace]
  refine ⟨28314607128543568233127205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18876404752362378822084803 28314607128543568233127205)
  ·
    refine ⟨5308988836601919043711351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28314607128543568233127205 5308988836601919043711351)
    ·
      refine ⟨7963483254902878565567027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5308988836601919043711351 7963483254902878565567027)
      ·
        refine ⟨11945224882354317848350541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7963483254902878565567027 11945224882354317848350541)
        ·
          refine ⟨4479459330882869193131453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11945224882354317848350541 4479459330882869193131453)
          ·
            refine ⟨1679797249081075947424295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4479459330882869193131453 1679797249081075947424295)
            ·
              refine ⟨2519695873621613921136443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679797249081075947424295 2519695873621613921136443)
              ·
                refine ⟨3779543810432420881704665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2519695873621613921136443 3779543810432420881704665)
                ·
                  refine ⟨2834657857824315661278499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3779543810432420881704665 2834657857824315661278499)
                  ·
                    refine ⟨4251986786736473491917749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2834657857824315661278499 4251986786736473491917749)
                    ·
                      refine ⟨398623761256544389867289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4251986786736473491917749 398623761256544389867289)
                      ·
                        rfl

theorem cell23_776317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_776317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776317 prefixEnd_776317 := by exact prefixLift 776317
  have htrace : WordTrace (prefixWord ++ tailWord_776317) baseStart_776317 baseEnd_776317 := by
    simpa [prefixWord, tailWord_776317, baseEnd_776317] using wordTrace_append hprefix tailTrace_776317
  have hstable : (prefixWord ++ tailWord_776317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776317).length < 2 ^ (prefixWord ++ tailWord_776317).sum := by decide
  have hdescent : baseEnd_776317 < baseStart_776317 := by decide
  rcases family_descends (prefixWord ++ tailWord_776317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776388 : List Nat := [2, 3, 3, 1, 2, 3, 2, 2, 5]
def baseStart_776388 : Nat := 118140960795 + 776388 * 2 ^ 59
def prefixEnd_776388 : Nat := 4983230072969 + 3 ^ 40 * 776388 * 2
def baseEnd_776388 : Nat := 44295579820334845786607

theorem tailTrace_776388 : CollatzResearch.WordTrace tailWord_776388 prefixEnd_776388 44295579820334845786607 := by
  unfold tailWord_776388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14158598355643173679480909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18878131140857564905974545 14158598355643173679480909)
  ·
    refine ⟨5309474383366190129805341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14158598355643173679480909 5309474383366190129805341)
    ·
      refine ⟨1991052893762321298677003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5309474383366190129805341 1991052893762321298677003)
      ·
        refine ⟨2986579340643481948015505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991052893762321298677003 2986579340643481948015505)
        ·
          refine ⟨2239934505482611461011629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2986579340643481948015505 2239934505482611461011629)
          ·
            refine ⟨839975439555979297879361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2239934505482611461011629 839975439555979297879361)
            ·
              refine ⟨629981579666984473409521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839975439555979297879361 629981579666984473409521)
              ·
                refine ⟨472486184750238355057141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629981579666984473409521 472486184750238355057141)
                ·
                  refine ⟨44295579820334845786607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 472486184750238355057141 44295579820334845786607)
                  ·
                    rfl

theorem cell23_776388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_776388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776388 prefixEnd_776388 := by exact prefixLift 776388
  have htrace : WordTrace (prefixWord ++ tailWord_776388) baseStart_776388 baseEnd_776388 := by
    simpa [prefixWord, tailWord_776388, baseEnd_776388] using wordTrace_append hprefix tailTrace_776388
  have hstable : (prefixWord ++ tailWord_776388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776388).length < 2 ^ (prefixWord ++ tailWord_776388).sum := by decide
  have hdescent : baseEnd_776388 < baseStart_776388 := by decide
  rcases family_descends (prefixWord ++ tailWord_776388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776407 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_776407 : Nat := 118140960795 + 776407 * 2 ^ 59
def prefixEnd_776407 : Nat := 4983230072969 + 3 ^ 40 * 776407 * 2
def baseEnd_776407 : Nat := 398669974515449037741875

theorem tailTrace_776407 : CollatzResearch.WordTrace tailWord_776407 prefixEnd_776407 398669974515449037741875 := by
  unfold tailWord_776407
  simp only [CollatzResearch.WordTrace]
  refine ⟨28317889698217513603903475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18878593132145009069268983 28317889698217513603903475)
  ·
    refine ⟨42476834547326270405855213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28317889698217513603903475 42476834547326270405855213)
    ·
      refine ⟨15928812955247351402195705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42476834547326270405855213 15928812955247351402195705)
      ·
        refine ⟨11946609716435513551646779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15928812955247351402195705 11946609716435513551646779)
        ·
          refine ⟨17919914574653270327470169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11946609716435513551646779 17919914574653270327470169)
          ·
            refine ⟨13439935930989952745602627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17919914574653270327470169 13439935930989952745602627)
            ·
              refine ⟨20159903896484929118403941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13439935930989952745602627 20159903896484929118403941)
              ·
                refine ⟨3779981980590924209700739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20159903896484929118403941 3779981980590924209700739)
                ·
                  refine ⟨5669972970886386314551109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779981980590924209700739 5669972970886386314551109)
                  ·
                    refine ⟨1063119932041197433978333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5669972970886386314551109 1063119932041197433978333)
                    ·
                      refine ⟨398669974515449037741875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1063119932041197433978333 398669974515449037741875)
                      ·
                        rfl

theorem cell23_776407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_776407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776407 prefixEnd_776407 := by exact prefixLift 776407
  have htrace : WordTrace (prefixWord ++ tailWord_776407) baseStart_776407 baseEnd_776407 := by
    simpa [prefixWord, tailWord_776407, baseEnd_776407] using wordTrace_append hprefix tailTrace_776407
  have hstable : (prefixWord ++ tailWord_776407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776407).length < 2 ^ (prefixWord ++ tailWord_776407).sum := by decide
  have hdescent : baseEnd_776407 < baseStart_776407 := by decide
  rcases family_descends (prefixWord ++ tailWord_776407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776418 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_776418 : Nat := 118140960795 + 776418 * 2 ^ 59
def prefixEnd_776418 : Nat := 4983230072969 + 3 ^ 40 * 776418 * 2
def baseEnd_776418 : Nat := 132891874267549498234775

theorem tailTrace_776418 : CollatzResearch.WordTrace tailWord_776418 prefixEnd_776418 132891874267549498234775 := by
  unfold tailWord_776418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7079572725294415620638477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18878860600785108321702605 7079572725294415620638477)
  ·
    refine ⟨2654839771985405857739429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7079572725294415620638477 2654839771985405857739429)
    ·
      refine ⟨497782457247263598326143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2654839771985405857739429 497782457247263598326143)
      ·
        refine ⟨746673685870895397489215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497782457247263598326143 746673685870895397489215)
        ·
          refine ⟨1120010528806343096233823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746673685870895397489215 1120010528806343096233823)
          ·
            refine ⟨1680015793209514644350735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120010528806343096233823 1680015793209514644350735)
            ·
              refine ⟨2520023689814271966526103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680015793209514644350735 2520023689814271966526103)
              ·
                refine ⟨3780035534721407949789155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520023689814271966526103 3780035534721407949789155)
                ·
                  refine ⟨5670053302082111924683733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780035534721407949789155 5670053302082111924683733)
                  ·
                    refine ⟨132891874267549498234775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5670053302082111924683733 132891874267549498234775)
                    ·
                      rfl

theorem cell23_776418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_776418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776418 prefixEnd_776418 := by exact prefixLift 776418
  have htrace : WordTrace (prefixWord ++ tailWord_776418) baseStart_776418 baseEnd_776418 := by
    simpa [prefixWord, tailWord_776418, baseEnd_776418] using wordTrace_append hprefix tailTrace_776418
  have hstable : (prefixWord ++ tailWord_776418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776418).length < 2 ^ (prefixWord ++ tailWord_776418).sum := by decide
  have hdescent : baseEnd_776418 < baseStart_776418 := by decide
  rcases family_descends (prefixWord ++ tailWord_776418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776421 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 4]
def baseStart_776421 : Nat := 118140960795 + 776421 * 2 ^ 59
def prefixEnd_776421 : Nat := 4983230072969 + 3 ^ 40 * 776421 * 2
def baseEnd_776421 : Nat := 398677163244611982966811

theorem tailTrace_776421 : CollatzResearch.WordTrace tailWord_776421 prefixEnd_776421 398677163244611982966811 := by
  unfold tailWord_776421
  simp only [CollatzResearch.WordTrace]
  refine ⟨28318400320166793994913117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18878933546777862663275411 28318400320166793994913117)
  ·
    refine ⟨10619400120062547748092419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28318400320166793994913117 10619400120062547748092419)
    ·
      refine ⟨15929100180093821622138629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10619400120062547748092419 15929100180093821622138629)
      ·
        refine ⟨2986706283767591554150993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15929100180093821622138629 2986706283767591554150993)
        ·
          refine ⟨2240029712825693665613245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2986706283767591554150993 2240029712825693665613245)
          ·
            refine ⟨840011142309635124604967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2240029712825693665613245 840011142309635124604967)
            ·
              refine ⟨1260016713464452686907451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840011142309635124604967 1260016713464452686907451)
              ·
                refine ⟨1890025070196679030361177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260016713464452686907451 1890025070196679030361177)
                ·
                  refine ⟨1417518802647509272770883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890025070196679030361177 1417518802647509272770883)
                  ·
                    refine ⟨2126278203971263909156325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1417518802647509272770883 2126278203971263909156325)
                    ·
                      refine ⟨398677163244611982966811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2126278203971263909156325 398677163244611982966811)
                      ·
                        rfl

theorem cell23_776421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_776421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776421 prefixEnd_776421 := by exact prefixLift 776421
  have htrace : WordTrace (prefixWord ++ tailWord_776421) baseStart_776421 baseEnd_776421 := by
    simpa [prefixWord, tailWord_776421, baseEnd_776421] using wordTrace_append hprefix tailTrace_776421
  have hstable : (prefixWord ++ tailWord_776421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776421).length < 2 ^ (prefixWord ++ tailWord_776421).sum := by decide
  have hdescent : baseEnd_776421 < baseStart_776421 := by decide
  rcases family_descends (prefixWord ++ tailWord_776421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776424 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_776424 : Nat := 118140960795 + 776424 * 2 ^ 59
def prefixEnd_776424 : Nat := 4983230072969 + 3 ^ 40 * 776424 * 2
def baseEnd_776424 : Nat := 398678703686575471229297

theorem tailTrace_776424 : CollatzResearch.WordTrace tailWord_776424 prefixEnd_776424 398678703686575471229297 := by
  unfold tailWord_776424
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159254869577962753636163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18879006492770617004848217 14159254869577962753636163)
  ·
    refine ⟨21238882304366944130454245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14159254869577962753636163 21238882304366944130454245)
    ·
      refine ⟨3982290432068802024460171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21238882304366944130454245 3982290432068802024460171)
      ·
        refine ⟨5973435648103203036690257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3982290432068802024460171 5973435648103203036690257)
        ·
          refine ⟨4480076736077402277517693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5973435648103203036690257 4480076736077402277517693)
          ·
            refine ⟨1680028776029025854069135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4480076736077402277517693 1680028776029025854069135)
            ·
              refine ⟨2520043164043538781103703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680028776029025854069135 2520043164043538781103703)
              ·
                refine ⟨3780064746065308171655555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520043164043538781103703 3780064746065308171655555)
                ·
                  refine ⟨5670097119097962257483333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780064746065308171655555 5670097119097962257483333)
                  ·
                    refine ⟨1063143209830867923278125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5670097119097962257483333 1063143209830867923278125)
                    ·
                      refine ⟨398678703686575471229297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1063143209830867923278125 398678703686575471229297)
                      ·
                        rfl

theorem cell23_776424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_776424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776424 prefixEnd_776424 := by exact prefixLift 776424
  have htrace : WordTrace (prefixWord ++ tailWord_776424) baseStart_776424 baseEnd_776424 := by
    simpa [prefixWord, tailWord_776424, baseEnd_776424] using wordTrace_append hprefix tailTrace_776424
  have hstable : (prefixWord ++ tailWord_776424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776424).length < 2 ^ (prefixWord ++ tailWord_776424).sum := by decide
  have hdescent : baseEnd_776424 < baseStart_776424 := by decide
  rcases family_descends (prefixWord ++ tailWord_776424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776431 : List Nat := [1, 1, 2, 1, 6, 1, 1, 5, 1, 4]
def baseStart_776431 : Nat := 118140960795 + 776431 * 2 ^ 59
def prefixEnd_776431 : Nat := 4983230072969 + 3 ^ 40 * 776431 * 2
def baseEnd_776431 : Nat := 132894099350385647947255

theorem tailTrace_776431 : CollatzResearch.WordTrace tailWord_776431 prefixEnd_776431 132894099350385647947255 := by
  unfold tailWord_776431
  simp only [CollatzResearch.WordTrace]
  refine ⟨28318765050130565702777147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18879176700087043801851431 28318765050130565702777147)
  ·
    refine ⟨42478147575195848554165721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28318765050130565702777147 42478147575195848554165721)
    ·
      refine ⟨31858610681396886415624291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42478147575195848554165721 31858610681396886415624291)
      ·
        refine ⟨47787916022095329623436437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31858610681396886415624291 47787916022095329623436437)
        ·
          refine ⟨2240058563535718576098583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47787916022095329623436437 2240058563535718576098583)
          ·
            refine ⟨3360087845303577864147875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240058563535718576098583 3360087845303577864147875)
            ·
              refine ⟨5040131767955366796221813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360087845303577864147875 5040131767955366796221813)
              ·
                refine ⟨472512353245815637145795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5040131767955366796221813 472512353245815637145795)
                ·
                  refine ⟨708768529868723455718693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472512353245815637145795 708768529868723455718693)
                  ·
                    refine ⟨132894099350385647947255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 708768529868723455718693 132894099350385647947255)
                    ·
                      rfl

theorem cell23_776431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 1, 4].length) (baseStart_776431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776431 prefixEnd_776431 := by exact prefixLift 776431
  have htrace : WordTrace (prefixWord ++ tailWord_776431) baseStart_776431 baseEnd_776431 := by
    simpa [prefixWord, tailWord_776431, baseEnd_776431] using wordTrace_append hprefix tailTrace_776431
  have hstable : (prefixWord ++ tailWord_776431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776431).length < 2 ^ (prefixWord ++ tailWord_776431).sum := by decide
  have hdescent : baseEnd_776431 < baseStart_776431 := by decide
  rcases family_descends (prefixWord ++ tailWord_776431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776444 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 6]
def baseStart_776444 : Nat := 118140960795 + 776444 * 2 ^ 59
def prefixEnd_776444 : Nat := 4983230072969 + 3 ^ 40 * 776444 * 2
def baseEnd_776444 : Nat := 44298774811073932553245

theorem tailTrace_776444 : CollatzResearch.WordTrace tailWord_776444 prefixEnd_776444 44298774811073932553245 := by
  unfold tailWord_776444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159619599541734461500193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18879492799388979282000257 14159619599541734461500193)
  ·
    refine ⟨10619714699656300846125145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14159619599541734461500193 10619714699656300846125145)
    ·
      refine ⟨7964786024742225634593859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10619714699656300846125145 7964786024742225634593859)
      ·
        refine ⟨11947179037113338451890789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7964786024742225634593859 11947179037113338451890789)
        ·
          refine ⟨2240096069458750959729523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11947179037113338451890789 2240096069458750959729523)
          ·
            refine ⟨3360144104188126439594285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240096069458750959729523 3360144104188126439594285)
            ·
              refine ⟨1260054039070547414847857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3360144104188126439594285 1260054039070547414847857)
              ·
                refine ⟨945040529302910561135893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260054039070547414847857 945040529302910561135893)
                ·
                  refine ⟨44298774811073932553245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 945040529302910561135893 44298774811073932553245)
                  ·
                    rfl

theorem cell23_776444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_776444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776444 prefixEnd_776444 := by exact prefixLift 776444
  have htrace : WordTrace (prefixWord ++ tailWord_776444) baseStart_776444 baseEnd_776444 := by
    simpa [prefixWord, tailWord_776444, baseEnd_776444] using wordTrace_append hprefix tailTrace_776444
  have hstable : (prefixWord ++ tailWord_776444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776444).length < 2 ^ (prefixWord ++ tailWord_776444).sum := by decide
  have hdescent : baseEnd_776444 < baseStart_776444 := by decide
  rcases family_descends (prefixWord ++ tailWord_776444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776471 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 3]
def baseStart_776471 : Nat := 118140960795 + 776471 * 2 ^ 59
def prefixEnd_776471 : Nat := 4983230072969 + 3 ^ 40 * 776471 * 2
def baseEnd_776471 : Nat := 398702837277336787341581

theorem tailTrace_776471 : CollatzResearch.WordTrace tailWord_776471 prefixEnd_776471 398702837277336787341581 := by
  unfold tailWord_776471
  simp only [CollatzResearch.WordTrace]
  refine ⟨28320223969985652534233267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18880149313323768356155511 28320223969985652534233267)
  ·
    refine ⟨42480335954978478801349901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28320223969985652534233267 42480335954978478801349901)
    ·
      refine ⟨15930125983116929550506213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42480335954978478801349901 15930125983116929550506213)
      ·
        refine ⟨2986898621834424290719915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15930125983116929550506213 2986898621834424290719915)
        ·
          refine ⟨4480347932751636436079873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986898621834424290719915 4480347932751636436079873)
          ·
            refine ⟨3360260949563727327059905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4480347932751636436079873 3360260949563727327059905)
            ·
              refine ⟨2520195712172795495294929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360260949563727327059905 2520195712172795495294929)
              ·
                refine ⟨1890146784129596621471197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520195712172795495294929 1890146784129596621471197)
                ·
                  refine ⟨708805044048598733051699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1890146784129596621471197 708805044048598733051699)
                  ·
                    refine ⟨1063207566072898099577549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 708805044048598733051699 1063207566072898099577549)
                    ·
                      refine ⟨398702837277336787341581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1063207566072898099577549 398702837277336787341581)
                      ·
                        rfl

theorem cell23_776471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_776471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776471 prefixEnd_776471 := by exact prefixLift 776471
  have htrace : WordTrace (prefixWord ++ tailWord_776471) baseStart_776471 baseEnd_776471 := by
    simpa [prefixWord, tailWord_776471, baseEnd_776471] using wordTrace_append hprefix tailTrace_776471
  have hstable : (prefixWord ++ tailWord_776471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776471).length < 2 ^ (prefixWord ++ tailWord_776471).sum := by decide
  have hdescent : baseEnd_776471 < baseStart_776471 := by decide
  rcases family_descends (prefixWord ++ tailWord_776471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776498 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_776498 : Nat := 118140960795 + 776498 * 2 ^ 59
def prefixEnd_776498 : Nat := 4983230072969 + 3 ^ 40 * 776498 * 2
def baseEnd_776498 : Nat := 398716701255008181703957

theorem tailTrace_776498 : CollatzResearch.WordTrace tailWord_776498 prefixEnd_776498 398716701255008181703957 := by
  unfold tailWord_776498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7080302185221959036366537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18880805827258557430310765 7080302185221959036366537)
  ·
    refine ⟨5310226638916469277274903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7080302185221959036366537 5310226638916469277274903)
    ·
      refine ⟨7965339958374703915912355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310226638916469277274903 7965339958374703915912355)
      ·
        refine ⟨11948009937562055873868533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965339958374703915912355 11948009937562055873868533)
        ·
          refine ⟨1120125931646442738175175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11948009937562055873868533 1120125931646442738175175)
          ·
            refine ⟨1680188897469664107262763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120125931646442738175175 1680188897469664107262763)
            ·
              refine ⟨2520283346204496160894145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680188897469664107262763 2520283346204496160894145)
              ·
                refine ⟨1890212509653372120670609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520283346204496160894145 1890212509653372120670609)
                ·
                  refine ⟨1417659382240029090502957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890212509653372120670609 1417659382240029090502957)
                  ·
                    refine ⟨531622268340010908938609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417659382240029090502957 531622268340010908938609)
                    ·
                      refine ⟨398716701255008181703957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531622268340010908938609 398716701255008181703957)
                      ·
                        rfl

theorem cell23_776498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_776498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776498 prefixEnd_776498 := by exact prefixLift 776498
  have htrace : WordTrace (prefixWord ++ tailWord_776498) baseStart_776498 baseEnd_776498 := by
    simpa [prefixWord, tailWord_776498, baseEnd_776498] using wordTrace_append hprefix tailTrace_776498
  have hstable : (prefixWord ++ tailWord_776498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776498).length < 2 ^ (prefixWord ++ tailWord_776498).sum := by decide
  have hdescent : baseEnd_776498 < baseStart_776498 := by decide
  rcases family_descends (prefixWord ++ tailWord_776498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776504 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 4, 4]
def baseStart_776504 : Nat := 118140960795 + 776504 * 2 ^ 59
def prefixEnd_776504 : Nat := 4983230072969 + 3 ^ 40 * 776504 * 2
def baseEnd_776504 : Nat := 132906594046311719409643

theorem tailTrace_776504 : CollatzResearch.WordTrace tailWord_776504 prefixEnd_776504 132906594046311719409643 := by
  unfold tailWord_776504
  simp only [CollatzResearch.WordTrace]
  refine ⟨14160713789433049585092283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18880951719244066113456377 14160713789433049585092283)
  ·
    refine ⟨21241070684149574377638425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14160713789433049585092283 21241070684149574377638425)
    ·
      refine ⟨15930803013112180783228819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21241070684149574377638425 15930803013112180783228819)
      ·
        refine ⟨23896204519668271174843229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15930803013112180783228819 23896204519668271174843229)
        ·
          refine ⟨8961076694875601690566211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23896204519668271174843229 8961076694875601690566211)
          ·
            refine ⟨13441615042313402535849317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961076694875601690566211 13441615042313402535849317)
            ·
              refine ⟨2520302820433762975471747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13441615042313402535849317 2520302820433762975471747)
              ·
                refine ⟨3780454230650644463207621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520302820433762975471747 3780454230650644463207621)
                ·
                  refine ⟨708835168246995836851429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3780454230650644463207621 708835168246995836851429)
                  ·
                    refine ⟨132906594046311719409643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 708835168246995836851429 132906594046311719409643)
                    ·
                      rfl

theorem cell23_776504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_776504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776504 prefixEnd_776504 := by exact prefixLift 776504
  have htrace : WordTrace (prefixWord ++ tailWord_776504) baseStart_776504 baseEnd_776504 := by
    simpa [prefixWord, tailWord_776504, baseEnd_776504] using wordTrace_append hprefix tailTrace_776504
  have hstable : (prefixWord ++ tailWord_776504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776504).length < 2 ^ (prefixWord ++ tailWord_776504).sum := by decide
  have hdescent : baseEnd_776504 < baseStart_776504 := by decide
  rcases family_descends (prefixWord ++ tailWord_776504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776524 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_776524 : Nat := 118140960795 + 776524 * 2 ^ 59
def prefixEnd_776524 : Nat := 4983230072969 + 3 ^ 40 * 776524 * 2
def baseEnd_776524 : Nat := 398730051752025079978837

theorem tailTrace_776524 : CollatzResearch.WordTrace tailWord_776524 prefixEnd_776524 398730051752025079978837 := by
  unfold tailWord_776524
  simp only [CollatzResearch.WordTrace]
  refine ⟨14161078519396821292956313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18881438025862428390608417 14161078519396821292956313)
  ·
    refine ⟨10620808889547615969717235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14161078519396821292956313 10620808889547615969717235)
    ·
      refine ⟨15931213334321423954575853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10620808889547615969717235 15931213334321423954575853)
      ·
        refine ⟨5974205000370533982965945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15931213334321423954575853 5974205000370533982965945)
        ·
          refine ⟨4480653750277900487224459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5974205000370533982965945 4480653750277900487224459)
          ·
            refine ⟨6720980625416850730836689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480653750277900487224459 6720980625416850730836689)
            ·
              refine ⟨5040735469062638048127517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720980625416850730836689 5040735469062638048127517)
              ·
                refine ⟨1890275800898489268047819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5040735469062638048127517 1890275800898489268047819)
                ·
                  refine ⟨2835413701347733902071729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890275800898489268047819 2835413701347733902071729)
                  ·
                    refine ⟨2126560276010800426553797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2835413701347733902071729 2126560276010800426553797)
                    ·
                      refine ⟨398730051752025079978837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2126560276010800426553797 398730051752025079978837)
                      ·
                        rfl

theorem cell23_776524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_776524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776524 prefixEnd_776524 := by exact prefixLift 776524
  have htrace : WordTrace (prefixWord ++ tailWord_776524) baseStart_776524 baseEnd_776524 := by
    simpa [prefixWord, tailWord_776524, baseEnd_776524] using wordTrace_append hprefix tailTrace_776524
  have hstable : (prefixWord ++ tailWord_776524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776524).length < 2 ^ (prefixWord ++ tailWord_776524).sum := by decide
  have hdescent : baseEnd_776524 < baseStart_776524 := by decide
  rcases family_descends (prefixWord ++ tailWord_776524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776548 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 1, 2, 3]
def baseStart_776548 : Nat := 118140960795 + 776548 * 2 ^ 59
def prefixEnd_776548 : Nat := 4983230072969 + 3 ^ 40 * 776548 * 2
def baseEnd_776548 : Nat := 398742375287732986078727

theorem tailTrace_776548 : CollatzResearch.WordTrace tailWord_776548 prefixEnd_776548 398742375287732986078727 := by
  unfold tailWord_776548
  simp only [CollatzResearch.WordTrace]
  refine ⟨14161516195353347342393149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18882021593804463123190865 14161516195353347342393149)
  ·
    refine ⟨5310568573257505253397431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14161516195353347342393149 5310568573257505253397431)
    ·
      refine ⟨7965852859886257880096147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310568573257505253397431 7965852859886257880096147)
      ·
        refine ⟨11948779289829386820144221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965852859886257880096147 11948779289829386820144221)
        ·
          refine ⟨4480792233686020057554083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11948779289829386820144221 4480792233686020057554083)
          ·
            refine ⟨6721188350529030086331125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480792233686020057554083 6721188350529030086331125)
            ·
              refine ⟨630111407862096570593543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6721188350529030086331125 630111407862096570593543)
              ·
                refine ⟨945167111793144855890315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630111407862096570593543 945167111793144855890315)
                ·
                  refine ⟨1417750667689717283835473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945167111793144855890315 1417750667689717283835473)
                  ·
                    refine ⟨1063313000767287962876605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1417750667689717283835473 1063313000767287962876605)
                    ·
                      refine ⟨398742375287732986078727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1063313000767287962876605 398742375287732986078727)
                      ·
                        rfl

theorem cell23_776548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_776548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776548 prefixEnd_776548 := by exact prefixLift 776548
  have htrace : WordTrace (prefixWord ++ tailWord_776548) baseStart_776548 baseEnd_776548 := by
    simpa [prefixWord, tailWord_776548, baseEnd_776548] using wordTrace_append hprefix tailTrace_776548
  have hstable : (prefixWord ++ tailWord_776548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776548).length < 2 ^ (prefixWord ++ tailWord_776548).sum := by decide
  have hdescent : baseEnd_776548 < baseStart_776548 := by decide
  rcases family_descends (prefixWord ++ tailWord_776548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776562 : List Nat := [3, 2, 1, 2, 1, 3, 4, 2, 1, 2, 2]
def baseStart_776562 : Nat := 118140960795 + 776562 * 2 ^ 59
def prefixEnd_776562 : Nat := 4983230072969 + 3 ^ 40 * 776562 * 2
def baseEnd_776562 : Nat := 398749564016895931303663

theorem tailTrace_776562 : CollatzResearch.WordTrace tailWord_776562 prefixEnd_776562 398749564016895931303663 := by
  unfold tailWord_776562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7080885753163993768948985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18882362008437316717197293 7080885753163993768948985)
  ·
    refine ⟨5310664314872995326711739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7080885753163993768948985 5310664314872995326711739)
    ·
      refine ⟨7965996472309492990067609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310664314872995326711739 7965996472309492990067609)
      ·
        refine ⟨5974497354232119742550707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7965996472309492990067609 5974497354232119742550707)
        ·
          refine ⟨8961746031348179613826061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5974497354232119742550707 8961746031348179613826061)
          ·
            refine ⟨3360654761755567355184773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8961746031348179613826061 3360654761755567355184773)
            ·
              refine ⟨630122767829168879097145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3360654761755567355184773 630122767829168879097145)
              ·
                refine ⟨472592075871876659322859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630122767829168879097145 472592075871876659322859)
                ·
                  refine ⟨708888113807814988984289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472592075871876659322859 708888113807814988984289)
                  ·
                    refine ⟨531666085355861241738217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 708888113807814988984289 531666085355861241738217)
                    ·
                      refine ⟨398749564016895931303663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531666085355861241738217 398749564016895931303663)
                      ·
                        rfl

theorem cell23_776562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_776562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776562 prefixEnd_776562 := by exact prefixLift 776562
  have htrace : WordTrace (prefixWord ++ tailWord_776562) baseStart_776562 baseEnd_776562 := by
    simpa [prefixWord, tailWord_776562, baseEnd_776562] using wordTrace_append hprefix tailTrace_776562
  have hstable : (prefixWord ++ tailWord_776562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776562).length < 2 ^ (prefixWord ++ tailWord_776562).sum := by decide
  have hdescent : baseEnd_776562 < baseStart_776562 := by decide
  rcases family_descends (prefixWord ++ tailWord_776562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776571 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 3, 3, 2]
def baseStart_776571 : Nat := 118140960795 + 776571 * 2 ^ 59
def prefixEnd_776571 : Nat := 4983230072969 + 3 ^ 40 * 776571 * 2
def baseEnd_776571 : Nat := 398754185342786396091121

theorem tailTrace_776571 : CollatzResearch.WordTrace tailWord_776571 prefixEnd_776571 398754185342786396091121 := by
  unfold tailWord_776571
  simp only [CollatzResearch.WordTrace]
  refine ⟨28323871269623369612873567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18882580846415579741915711 28323871269623369612873567)
  ·
    refine ⟨42485806904435054419310351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28323871269623369612873567 42485806904435054419310351)
    ·
      refine ⟨63728710356652581628965527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42485806904435054419310351 63728710356652581628965527)
      ·
        refine ⟨95593065534978872443448291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63728710356652581628965527 95593065534978872443448291)
        ·
          refine ⟨143389598302468308665172437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95593065534978872443448291 143389598302468308665172437)
          ·
            refine ⟨3360693710214100984339979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 143389598302468308665172437 3360693710214100984339979)
            ·
              refine ⟨5041040565321151476509969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360693710214100984339979 5041040565321151476509969)
              ·
                refine ⟨3780780423990863607382477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5041040565321151476509969 3780780423990863607382477)
                ·
                  refine ⟨1417792658996573852768429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3780780423990863607382477 1417792658996573852768429)
                  ·
                    refine ⟨531672247123715194788161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417792658996573852768429 531672247123715194788161)
                    ·
                      refine ⟨398754185342786396091121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531672247123715194788161 398754185342786396091121)
                      ·
                        rfl

theorem cell23_776571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 3, 2].length) (baseStart_776571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776571 prefixEnd_776571 := by exact prefixLift 776571
  have htrace : WordTrace (prefixWord ++ tailWord_776571) baseStart_776571 baseEnd_776571 := by
    simpa [prefixWord, tailWord_776571, baseEnd_776571] using wordTrace_append hprefix tailTrace_776571
  have hstable : (prefixWord ++ tailWord_776571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776571).length < 2 ^ (prefixWord ++ tailWord_776571).sum := by decide
  have hdescent : baseEnd_776571 < baseStart_776571 := by decide
  rcases family_descends (prefixWord ++ tailWord_776571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776584 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_776584 : Nat := 118140960795 + 776584 * 2 ^ 59
def prefixEnd_776584 : Nat := 4983230072969 + 3 ^ 40 * 776584 * 2
def baseEnd_776584 : Nat := 398760860591294845228561

theorem tailTrace_776584 : CollatzResearch.WordTrace tailWord_776584 prefixEnd_776584 398760860591294845228561 := by
  unfold tailWord_776584
  simp only [CollatzResearch.WordTrace]
  refine ⟨14162172709288136416548403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18882896945717515222064537 14162172709288136416548403)
  ·
    refine ⟨21243259063932204624822605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14162172709288136416548403 21243259063932204624822605)
    ·
      refine ⟨7966222148974576734308477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21243259063932204624822605 7966222148974576734308477)
      ·
        refine ⟨2987333305865466275365679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7966222148974576734308477 2987333305865466275365679)
        ·
          refine ⟨4480999958798199413048519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987333305865466275365679 4480999958798199413048519)
          ·
            refine ⟨6721499938197299119572779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480999958798199413048519 6721499938197299119572779)
            ·
              refine ⟨10082249907295948679359169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6721499938197299119572779 10082249907295948679359169)
              ·
                refine ⟨7561687430471961509519377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10082249907295948679359169 7561687430471961509519377)
                ·
                  refine ⟨5671265572853971132139533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7561687430471961509519377 5671265572853971132139533)
                  ·
                    refine ⟨2126724589820239174552325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5671265572853971132139533 2126724589820239174552325)
                    ·
                      refine ⟨398760860591294845228561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2126724589820239174552325 398760860591294845228561)
                      ·
                        rfl

theorem cell23_776584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_776584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776584 prefixEnd_776584 := by exact prefixLift 776584
  have htrace : WordTrace (prefixWord ++ tailWord_776584) baseStart_776584 baseEnd_776584 := by
    simpa [prefixWord, tailWord_776584, baseEnd_776584] using wordTrace_append hprefix tailTrace_776584
  have hstable : (prefixWord ++ tailWord_776584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776584).length < 2 ^ (prefixWord ++ tailWord_776584).sum := by decide
  have hdescent : baseEnd_776584 < baseStart_776584 := by decide
  rcases family_descends (prefixWord ++ tailWord_776584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776601 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 1, 4, 2]
def baseStart_776601 : Nat := 118140960795 + 776601 * 2 ^ 59
def prefixEnd_776601 : Nat := 4983230072969 + 3 ^ 40 * 776601 * 2
def baseEnd_776601 : Nat := 398769589762421278715983

theorem tailTrace_776601 : CollatzResearch.WordTrace tailWord_776601 prefixEnd_776601 398769589762421278715983 := by
  unfold tailWord_776601
  simp only [CollatzResearch.WordTrace]
  refine ⟨28324965459514684736465657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18883310306343123157643771 28324965459514684736465657)
  ·
    refine ⟨21243724094636013552349243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28324965459514684736465657 21243724094636013552349243)
    ·
      refine ⟨31865586141954020328523865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21243724094636013552349243 31865586141954020328523865)
      ·
        refine ⟨23899189606465515246392899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31865586141954020328523865 23899189606465515246392899)
        ·
          refine ⟨35848784409698272869589349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23899189606465515246392899 35848784409698272869589349)
          ·
            refine ⟨6721647076818426163048003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35848784409698272869589349 6721647076818426163048003)
            ·
              refine ⟨10082470615227639244572005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6721647076818426163048003 10082470615227639244572005)
              ·
                refine ⟨1890463240355182358357251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10082470615227639244572005 1890463240355182358357251)
                ·
                  refine ⟨2835694860532773537535877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890463240355182358357251 2835694860532773537535877)
                  ·
                    refine ⟨531692786349895038287977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2835694860532773537535877 531692786349895038287977)
                    ·
                      refine ⟨398769589762421278715983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531692786349895038287977 398769589762421278715983)
                      ·
                        rfl

theorem cell23_776601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_776601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776601 prefixEnd_776601 := by exact prefixLift 776601
  have htrace : WordTrace (prefixWord ++ tailWord_776601) baseStart_776601 baseEnd_776601 := by
    simpa [prefixWord, tailWord_776601, baseEnd_776601] using wordTrace_append hprefix tailTrace_776601
  have hstable : (prefixWord ++ tailWord_776601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776601).length < 2 ^ (prefixWord ++ tailWord_776601).sum := by decide
  have hdescent : baseEnd_776601 < baseStart_776601 := by decide
  rcases family_descends (prefixWord ++ tailWord_776601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776605 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_776605 : Nat := 118140960795 + 776605 * 2 ^ 59
def prefixEnd_776605 : Nat := 4983230072969 + 3 ^ 40 * 776605 * 2
def baseEnd_776605 : Nat := 398771643685039263065965

theorem tailTrace_776605 : CollatzResearch.WordTrace tailWord_776605 prefixEnd_776605 398771643685039263065965 := by
  unfold tailWord_776605
  simp only [CollatzResearch.WordTrace]
  refine ⟨28325111351500193419611269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18883407567666795613074179 28325111351500193419611269)
  ·
    refine ⟨5310958378406286266177113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28325111351500193419611269 5310958378406286266177113)
    ·
      refine ⟨3983218783804714699632835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5310958378406286266177113 3983218783804714699632835)
      ·
        refine ⟨5974828175707072049449253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3983218783804714699632835 5974828175707072049449253)
        ·
          refine ⟨1120280282945076009271735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5974828175707072049449253 1120280282945076009271735)
          ·
            refine ⟨1680420424417614013907603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120280282945076009271735 1680420424417614013907603)
            ·
              refine ⟨2520630636626421020861405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680420424417614013907603 2520630636626421020861405)
              ·
                refine ⟨945236488734907882823027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2520630636626421020861405 945236488734907882823027)
                ·
                  refine ⟨1417854733102361824234541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945236488734907882823027 1417854733102361824234541)
                  ·
                    refine ⟨531695524913385684087953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417854733102361824234541 531695524913385684087953)
                    ·
                      refine ⟨398771643685039263065965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531695524913385684087953 398771643685039263065965)
                      ·
                        rfl

theorem cell23_776605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_776605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776605 prefixEnd_776605 := by exact prefixLift 776605
  have htrace : WordTrace (prefixWord ++ tailWord_776605) baseStart_776605 baseEnd_776605 := by
    simpa [prefixWord, tailWord_776605, baseEnd_776605] using wordTrace_append hprefix tailTrace_776605
  have hstable : (prefixWord ++ tailWord_776605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776605).length < 2 ^ (prefixWord ++ tailWord_776605).sum := by decide
  have hdescent : baseEnd_776605 < baseStart_776605 := by decide
  rcases family_descends (prefixWord ++ tailWord_776605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776664 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_776664 : Nat := 118140960795 + 776664 * 2 ^ 59
def prefixEnd_776664 : Nat := 4983230072969 + 3 ^ 40 * 776664 * 2
def baseEnd_776664 : Nat := 398801939043654532228193

theorem tailTrace_776664 : CollatzResearch.WordTrace tailWord_776664 prefixEnd_776664 398801939043654532228193 := by
  unfold tailWord_776664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14163631629143223248004523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18884842172190964330672697 14163631629143223248004523)
  ·
    refine ⟨21245447443714834872006785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14163631629143223248004523 21245447443714834872006785)
    ·
      refine ⟨15934085582786126154005089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21245447443714834872006785 15934085582786126154005089)
      ·
        refine ⟨11950564187089594615503817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15934085582786126154005089 11950564187089594615503817)
        ·
          refine ⟨8962923140317195961627863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11950564187089594615503817 8962923140317195961627863)
          ·
            refine ⟨13444384710475793942441795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8962923140317195961627863 13444384710475793942441795)
            ·
              refine ⟨20166577065713690913662693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13444384710475793942441795 20166577065713690913662693)
              ·
                refine ⟨3781233199821317046311755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20166577065713690913662693 3781233199821317046311755)
                ·
                  refine ⟨5671849799731975569467633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3781233199821317046311755 5671849799731975569467633)
                  ·
                    refine ⟨4253887349798981677100725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5671849799731975569467633 4253887349798981677100725)
                    ·
                      refine ⟨398801939043654532228193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4253887349798981677100725 398801939043654532228193)
                      ·
                        rfl

theorem cell23_776664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_776664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776664 prefixEnd_776664 := by exact prefixLift 776664
  have htrace : WordTrace (prefixWord ++ tailWord_776664) baseStart_776664 baseEnd_776664 := by
    simpa [prefixWord, tailWord_776664, baseEnd_776664] using wordTrace_append hprefix tailTrace_776664
  have hstable : (prefixWord ++ tailWord_776664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776664).length < 2 ^ (prefixWord ++ tailWord_776664).sum := by decide
  have hdescent : baseEnd_776664 < baseStart_776664 := by decide
  rcases family_descends (prefixWord ++ tailWord_776664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776671 : List Nat := [1, 1, 2, 3, 3, 3, 1, 2, 2, 5]
def baseStart_776671 : Nat := 118140960795 + 776671 * 2 ^ 59
def prefixEnd_776671 : Nat := 4983230072969 + 3 ^ 40 * 776671 * 2
def baseEnd_776671 : Nat := 132935177802745334946887

theorem tailTrace_776671 : CollatzResearch.WordTrace tailWord_776671 prefixEnd_776671 132935177802745334946887 := by
  unfold tailWord_776671
  simp only [CollatzResearch.WordTrace]
  refine ⟨28327518569261086691513867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18885012379507391127675911 28327518569261086691513867)
  ·
    refine ⟨42491277853891630037270801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28327518569261086691513867 42491277853891630037270801)
    ·
      refine ⟨31868458390418722527953101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42491277853891630037270801 31868458390418722527953101)
      ·
        refine ⟨11950671896407020947982413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31868458390418722527953101 11950671896407020947982413)
        ·
          refine ⟨4481501961152632855493405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11950671896407020947982413 4481501961152632855493405)
          ·
            refine ⟨1680563235432237320810027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4481501961152632855493405 1680563235432237320810027)
            ·
              refine ⟨2520844853148355981215041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680563235432237320810027 2520844853148355981215041)
              ·
                refine ⟨1890633639861266985911281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520844853148355981215041 1890633639861266985911281)
                ·
                  refine ⟨1417975229895950239433461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890633639861266985911281 1417975229895950239433461)
                  ·
                    refine ⟨132935177802745334946887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1417975229895950239433461 132935177802745334946887)
                    ·
                      rfl

theorem cell23_776671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_776671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776671 prefixEnd_776671 := by exact prefixLift 776671
  have htrace : WordTrace (prefixWord ++ tailWord_776671) baseStart_776671 baseEnd_776671 := by
    simpa [prefixWord, tailWord_776671, baseEnd_776671] using wordTrace_append hprefix tailTrace_776671
  have hstable : (prefixWord ++ tailWord_776671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776671).length < 2 ^ (prefixWord ++ tailWord_776671).sum := by decide
  have hdescent : baseEnd_776671 < baseStart_776671 := by decide
  rcases family_descends (prefixWord ++ tailWord_776671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776675 : List Nat := [1, 1, 1, 6, 3, 1, 3, 2, 5]
def baseStart_776675 : Nat := 118140960795 + 776675 * 2 ^ 59
def prefixEnd_776675 : Nat := 4983230072969 + 3 ^ 40 * 776675 * 2
def baseEnd_776675 : Nat := 44311954147872665465627

theorem tailTrace_776675 : CollatzResearch.WordTrace tailWord_776675 prefixEnd_776675 44311954147872665465627 := by
  unfold tailWord_776675
  simp only [CollatzResearch.WordTrace]
  refine ⟨28327664461246595374659479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18885109640831063583106319 28327664461246595374659479)
  ·
    refine ⟨42491496691869893061989219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28327664461246595374659479 42491496691869893061989219)
    ·
      refine ⟨63737245037804839592983829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42491496691869893061989219 63737245037804839592983829)
      ·
        refine ⟨2987683361147101855921117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63737245037804839592983829 2987683361147101855921117)
        ·
          refine ⟨1120381260430163195970419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2987683361147101855921117 1120381260430163195970419)
          ·
            refine ⟨1680571890645244793955629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120381260430163195970419 1680571890645244793955629)
            ·
              refine ⟨630214458991966797733361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1680571890645244793955629 630214458991966797733361)
              ·
                refine ⟨472660844243975098300021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 630214458991966797733361 472660844243975098300021)
                ·
                  refine ⟨44311954147872665465627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 472660844243975098300021 44311954147872665465627)
                  ·
                    rfl

theorem cell23_776675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 5].length) (baseStart_776675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776675 prefixEnd_776675 := by exact prefixLift 776675
  have htrace : WordTrace (prefixWord ++ tailWord_776675) baseStart_776675 baseEnd_776675 := by
    simpa [prefixWord, tailWord_776675, baseEnd_776675] using wordTrace_append hprefix tailTrace_776675
  have hstable : (prefixWord ++ tailWord_776675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776675).length < 2 ^ (prefixWord ++ tailWord_776675).sum := by decide
  have hdescent : baseEnd_776675 < baseStart_776675 := by decide
  rcases family_descends (prefixWord ++ tailWord_776675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776691 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 1, 6, 2]
def baseStart_776691 : Nat := 118140960795 + 776691 * 2 ^ 59
def prefixEnd_776691 : Nat := 4983230072969 + 3 ^ 40 * 776691 * 2
def baseEnd_776691 : Nat := 398815803021325926590569

theorem tailTrace_776691 : CollatzResearch.WordTrace tailWord_776691 prefixEnd_776691 398815803021325926590569 := by
  unfold tailWord_776691
  simp only [CollatzResearch.WordTrace]
  refine ⟨28328248029188630107241927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18885498686125753404827951 28328248029188630107241927)
  ·
    refine ⟨42492372043782945160862891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28328248029188630107241927 42492372043782945160862891)
    ·
      refine ⟨63738558065674417741294337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42492372043782945160862891 63738558065674417741294337)
      ·
        refine ⟨47803918549255813305970753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63738558065674417741294337 47803918549255813305970753)
        ·
          refine ⟨35852938911941859979478065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47803918549255813305970753 35852938911941859979478065)
          ·
            refine ⟨26889704183956394984608549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35852938911941859979478065 26889704183956394984608549)
            ·
              refine ⟨5041819534491824059614103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26889704183956394984608549 5041819534491824059614103)
              ·
                refine ⟨7562729301737736089421155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041819534491824059614103 7562729301737736089421155)
                ·
                  refine ⟨11344093952606604134131733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7562729301737736089421155 11344093952606604134131733)
                  ·
                    refine ⟨531754404028434568787425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11344093952606604134131733 531754404028434568787425)
                    ·
                      refine ⟨398815803021325926590569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531754404028434568787425 398815803021325926590569)
                      ·
                        rfl

theorem cell23_776691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 6, 2].length) (baseStart_776691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776691 prefixEnd_776691 := by exact prefixLift 776691
  have htrace : WordTrace (prefixWord ++ tailWord_776691) baseStart_776691 baseEnd_776691 := by
    simpa [prefixWord, tailWord_776691, baseEnd_776691] using wordTrace_append hprefix tailTrace_776691
  have hstable : (prefixWord ++ tailWord_776691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776691).length < 2 ^ (prefixWord ++ tailWord_776691).sum := by decide
  have hdescent : baseEnd_776691 < baseStart_776691 := by decide
  rcases family_descends (prefixWord ++ tailWord_776691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776701 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_776701 : Nat := 118140960795 + 776701 * 2 ^ 59
def prefixEnd_776701 : Nat := 4983230072969 + 3 ^ 40 * 776701 * 2
def baseEnd_776701 : Nat := 132940312609290295821841

theorem tailTrace_776701 : CollatzResearch.WordTrace tailWord_776701 prefixEnd_776701 132940312609290295821841 := by
  unfold tailWord_776701
  simp only [CollatzResearch.WordTrace]
  refine ⟨28328612759152401815105957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18885741839434934543403971 28328612759152401815105957)
  ·
    refine ⟨5311614892341075340332367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28328612759152401815105957 5311614892341075340332367)
    ·
      refine ⟨7967422338511613010498551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5311614892341075340332367 7967422338511613010498551)
      ·
        refine ⟨11951133507767419515747827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967422338511613010498551 11951133507767419515747827)
        ·
          refine ⟨17926700261651129273621741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11951133507767419515747827 17926700261651129273621741)
          ·
            refine ⟨6722512598119173477608153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17926700261651129273621741 6722512598119173477608153)
            ·
              refine ⟨5041884448589380108206115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6722512598119173477608153 5041884448589380108206115)
              ·
                refine ⟨7562826672884070162309173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5041884448589380108206115 7562826672884070162309173)
                ·
                  refine ⟨709015000582881577716485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7562826672884070162309173 709015000582881577716485)
                  ·
                    refine ⟨132940312609290295821841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 709015000582881577716485 132940312609290295821841)
                    ·
                      rfl

theorem cell23_776701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_776701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776701 prefixEnd_776701 := by exact prefixLift 776701
  have htrace : WordTrace (prefixWord ++ tailWord_776701) baseStart_776701 baseEnd_776701 := by
    simpa [prefixWord, tailWord_776701, baseEnd_776701] using wordTrace_append hprefix tailTrace_776701
  have hstable : (prefixWord ++ tailWord_776701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776701).length < 2 ^ (prefixWord ++ tailWord_776701).sum := by decide
  have hdescent : baseEnd_776701 < baseStart_776701 := by decide
  rcases family_descends (prefixWord ++ tailWord_776701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776708 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_776708 : Nat := 118140960795 + 776708 * 2 ^ 59
def prefixEnd_776708 : Nat := 4983230072969 + 3 ^ 40 * 776708 * 2
def baseEnd_776708 : Nat := 398824532192452360077991

theorem tailTrace_776708 : CollatzResearch.WordTrace tailWord_776708 prefixEnd_776708 398824532192452360077991 := by
  unfold tailWord_776708
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164434035063521005305389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18885912046751361340407185 14164434035063521005305389)
  ·
    refine ⟨5311662763148820376989521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14164434035063521005305389 5311662763148820376989521)
    ·
      refine ⟨3983747072361615282742141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5311662763148820376989521 3983747072361615282742141)
      ·
        refine ⟨1493905152135605731028303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3983747072361615282742141 1493905152135605731028303)
        ·
          refine ⟨2240857728203408596542455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493905152135605731028303 2240857728203408596542455)
          ·
            refine ⟨3361286592305112894813683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240857728203408596542455 3361286592305112894813683)
            ·
              refine ⟨5041929888457669342220525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361286592305112894813683 5041929888457669342220525)
              ·
                refine ⟨1890723708171626003332697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5041929888457669342220525 1890723708171626003332697)
                ·
                  refine ⟨1418042781128719502499523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890723708171626003332697 1418042781128719502499523)
                  ·
                    refine ⟨2127064171693079253749285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1418042781128719502499523 2127064171693079253749285)
                    ·
                      refine ⟨398824532192452360077991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2127064171693079253749285 398824532192452360077991)
                      ·
                        rfl

theorem cell23_776708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_776708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776708 prefixEnd_776708 := by exact prefixLift 776708
  have htrace : WordTrace (prefixWord ++ tailWord_776708) baseStart_776708 baseEnd_776708 := by
    simpa [prefixWord, tailWord_776708, baseEnd_776708] using wordTrace_append hprefix tailTrace_776708
  have hstable : (prefixWord ++ tailWord_776708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776708).length < 2 ^ (prefixWord ++ tailWord_776708).sum := by decide
  have hdescent : baseEnd_776708 < baseStart_776708 := by decide
  rcases family_descends (prefixWord ++ tailWord_776708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776728 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_776728 : Nat := 118140960795 + 776728 * 2 ^ 59
def prefixEnd_776728 : Nat := 4983230072969 + 3 ^ 40 * 776728 * 2
def baseEnd_776728 : Nat := 398834801805542281827899

theorem tailTrace_776728 : CollatzResearch.WordTrace tailWord_776728 prefixEnd_776728 398834801805542281827899 := by
  unfold tailWord_776728
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164798765027292713169419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18886398353369723617559225 14164798765027292713169419)
  ·
    refine ⟨21247198147540939069754129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14164798765027292713169419 21247198147540939069754129)
    ·
      refine ⟨15935398610655704302315597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21247198147540939069754129 15935398610655704302315597)
      ·
        refine ⟨5975774478995889113368349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15935398610655704302315597 5975774478995889113368349)
        ·
          refine ⟨2240915429623458417513131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5975774478995889113368349 2240915429623458417513131)
          ·
            refine ⟨3361373144435187626269697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240915429623458417513131 3361373144435187626269697)
            ·
              refine ⟨2521029858326390719702273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3361373144435187626269697 2521029858326390719702273)
              ·
                refine ⟨1890772393744793039776705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521029858326390719702273 1890772393744793039776705)
                ·
                  refine ⟨1418079295308594779832529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890772393744793039776705 1418079295308594779832529)
                  ·
                    refine ⟨1063559471481446084874397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1418079295308594779832529 1063559471481446084874397)
                    ·
                      refine ⟨398834801805542281827899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1063559471481446084874397 398834801805542281827899)
                      ·
                        rfl

theorem cell23_776728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_776728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776728 prefixEnd_776728 := by exact prefixLift 776728
  have htrace : WordTrace (prefixWord ++ tailWord_776728) baseStart_776728 baseEnd_776728 := by
    simpa [prefixWord, tailWord_776728, baseEnd_776728] using wordTrace_append hprefix tailTrace_776728
  have hstable : (prefixWord ++ tailWord_776728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776728).length < 2 ^ (prefixWord ++ tailWord_776728).sum := by decide
  have hdescent : baseEnd_776728 < baseStart_776728 := by decide
  rcases family_descends (prefixWord ++ tailWord_776728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776761 : List Nat := [1, 2, 1, 5, 1, 1, 1, 3, 3, 5]
def baseStart_776761 : Nat := 118140960795 + 776761 * 2 ^ 59
def prefixEnd_776761 : Nat := 4983230072969 + 3 ^ 40 * 776761 * 2
def baseEnd_776761 : Nat := 132950582222380217571749

theorem tailTrace_776761 : CollatzResearch.WordTrace tailWord_776761 prefixEnd_776761 132950582222380217571749 := by
  unfold tailWord_776761
  simp only [CollatzResearch.WordTrace]
  refine ⟨28330801138935032062290137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18887200759290021374860091 28330801138935032062290137)
  ·
    refine ⟨21248100854201274046717603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28330801138935032062290137 21248100854201274046717603)
    ·
      refine ⟨31872151281301911070076405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21248100854201274046717603 31872151281301911070076405)
      ·
        refine ⟨2988014182622054162819663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31872151281301911070076405 2988014182622054162819663)
        ·
          refine ⟨4482021273933081244229495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988014182622054162819663 4482021273933081244229495)
          ·
            refine ⟨6723031910899621866344243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4482021273933081244229495 6723031910899621866344243)
            ·
              refine ⟨10084547866349432799516365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723031910899621866344243 10084547866349432799516365)
              ·
                refine ⟨3781705449881037299818637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10084547866349432799516365 3781705449881037299818637)
                ·
                  refine ⟨1418139543705388987431989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3781705449881037299818637 1418139543705388987431989)
                  ·
                    refine ⟨132950582222380217571749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1418139543705388987431989 132950582222380217571749)
                    ·
                      rfl

theorem cell23_776761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 5].length) (baseStart_776761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776761 prefixEnd_776761 := by exact prefixLift 776761
  have htrace : WordTrace (prefixWord ++ tailWord_776761) baseStart_776761 baseEnd_776761 := by
    simpa [prefixWord, tailWord_776761, baseEnd_776761] using wordTrace_append hprefix tailTrace_776761
  have hstable : (prefixWord ++ tailWord_776761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776761).length < 2 ^ (prefixWord ++ tailWord_776761).sum := by decide
  have hdescent : baseEnd_776761 < baseStart_776761 := by decide
  rcases family_descends (prefixWord ++ tailWord_776761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776778 : List Nat := [3, 1, 2, 1, 1, 5, 1, 3, 1, 5]
def baseStart_776778 : Nat := 118140960795 + 776778 * 2 ^ 59
def prefixEnd_776778 : Nat := 4983230072969 + 3 ^ 40 * 776778 * 2
def baseEnd_776778 : Nat := 132953491946089028734223

theorem tailTrace_776778 : CollatzResearch.WordTrace tailWord_776778 prefixEnd_776778 132953491946089028734223 := by
  unfold tailWord_776778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7082855294968360991414747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18887614119915629310439325 7082855294968360991414747)
  ·
    refine ⟨10624282942452541487122121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7082855294968360991414747 10624282942452541487122121)
    ·
      refine ⟨7968212206839406115341591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10624282942452541487122121 7968212206839406115341591)
      ·
        refine ⟨11952318310259109173012387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7968212206839406115341591 11952318310259109173012387)
        ·
          refine ⟨17928477465388663759518581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11952318310259109173012387 17928477465388663759518581)
          ·
            refine ⟨1680794762380187227454867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17928477465388663759518581 1680794762380187227454867)
            ·
              refine ⟨2521192143570280841182301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680794762380187227454867 2521192143570280841182301)
              ·
                refine ⟨945447053838855315443363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2521192143570280841182301 945447053838855315443363)
                ·
                  refine ⟨1418170580758282973165045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945447053838855315443363 1418170580758282973165045)
                  ·
                    refine ⟨132953491946089028734223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1418170580758282973165045 132953491946089028734223)
                    ·
                      rfl

theorem cell23_776778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_776778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776778 prefixEnd_776778 := by exact prefixLift 776778
  have htrace : WordTrace (prefixWord ++ tailWord_776778) baseStart_776778 baseEnd_776778 := by
    simpa [prefixWord, tailWord_776778, baseEnd_776778] using wordTrace_append hprefix tailTrace_776778
  have hstable : (prefixWord ++ tailWord_776778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776778).length < 2 ^ (prefixWord ++ tailWord_776778).sum := by decide
  have hdescent : baseEnd_776778 < baseStart_776778 := by decide
  rcases family_descends (prefixWord ++ tailWord_776778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776801 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_776801 : Nat := 118140960795 + 776801 * 2 ^ 59
def prefixEnd_776801 : Nat := 4983230072969 + 3 ^ 40 * 776801 * 2
def baseEnd_776801 : Nat := 398872285893320496215063

theorem tailTrace_776801 : CollatzResearch.WordTrace tailWord_776801 prefixEnd_776801 398872285893320496215063 := by
  unfold tailWord_776801
  simp only [CollatzResearch.WordTrace]
  refine ⟨28332260058790118893746257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18888173372526745929164171 28332260058790118893746257)
  ·
    refine ⟨21249195044092589170309693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28332260058790118893746257 21249195044092589170309693)
    ·
      refine ⟨7968448141534720938866135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21249195044092589170309693 7968448141534720938866135)
      ·
        refine ⟨11952672212302081408299203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7968448141534720938866135 11952672212302081408299203)
        ·
          refine ⟨17929008318453122112448805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11952672212302081408299203 17929008318453122112448805)
          ·
            refine ⟨3361689059709960396084151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17929008318453122112448805 3361689059709960396084151)
            ·
              refine ⟨5042533589564940594126227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3361689059709960396084151 5042533589564940594126227)
              ·
                refine ⟨7563800384347410891189341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5042533589564940594126227 7563800384347410891189341)
                ·
                  refine ⟨2836425144130279084196003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7563800384347410891189341 2836425144130279084196003)
                  ·
                    refine ⟨4254637716195418626294005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2836425144130279084196003 4254637716195418626294005)
                    ·
                      refine ⟨398872285893320496215063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4254637716195418626294005 398872285893320496215063)
                      ·
                        rfl

theorem cell23_776801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_776801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776801 prefixEnd_776801 := by exact prefixLift 776801
  have htrace : WordTrace (prefixWord ++ tailWord_776801) baseStart_776801 baseEnd_776801 := by
    simpa [prefixWord, tailWord_776801, baseEnd_776801] using wordTrace_append hprefix tailTrace_776801
  have hstable : (prefixWord ++ tailWord_776801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776801).length < 2 ^ (prefixWord ++ tailWord_776801).sum := by decide
  have hdescent : baseEnd_776801 < baseStart_776801 := by decide
  rcases family_descends (prefixWord ++ tailWord_776801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776811 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 4]
def baseStart_776811 : Nat := 118140960795 + 776811 * 2 ^ 59
def prefixEnd_776811 : Nat := 4983230072969 + 3 ^ 40 * 776811 * 2
def baseEnd_776811 : Nat := 398877420699865457090017

theorem tailTrace_776811 : CollatzResearch.WordTrace tailWord_776811 prefixEnd_776811 398877420699865457090017 := by
  unfold tailWord_776811
  simp only [CollatzResearch.WordTrace]
  refine ⟨28332624788753890601610287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18888416525835927067740191 28332624788753890601610287)
  ·
    refine ⟨42498937183130835902415431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28332624788753890601610287 42498937183130835902415431)
    ·
      refine ⟨63748405774696253853623147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42498937183130835902415431 63748405774696253853623147)
      ·
        refine ⟨95622608662044380780434721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63748405774696253853623147 95622608662044380780434721)
        ·
          refine ⟨71716956496533285585326041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95622608662044380780434721 71716956496533285585326041)
          ·
            refine ⟨53787717372399964188994531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71716956496533285585326041 53787717372399964188994531)
            ·
              refine ⟨80681576058599946283491797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53787717372399964188994531 80681576058599946283491797)
              ·
                refine ⟨1890974438873436241019339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80681576058599946283491797 1890974438873436241019339)
                ·
                  refine ⟨2836461658310154361529009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890974438873436241019339 2836461658310154361529009)
                  ·
                    refine ⟨2127346243732615771146757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2836461658310154361529009 2127346243732615771146757)
                    ·
                      refine ⟨398877420699865457090017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2127346243732615771146757 398877420699865457090017)
                      ·
                        rfl

theorem cell23_776811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 4].length) (baseStart_776811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776811 prefixEnd_776811 := by exact prefixLift 776811
  have htrace : WordTrace (prefixWord ++ tailWord_776811) baseStart_776811 baseEnd_776811 := by
    simpa [prefixWord, tailWord_776811, baseEnd_776811] using wordTrace_append hprefix tailTrace_776811
  have hstable : (prefixWord ++ tailWord_776811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776811).length < 2 ^ (prefixWord ++ tailWord_776811).sum := by decide
  have hdescent : baseEnd_776811 < baseStart_776811 := by decide
  rcases family_descends (prefixWord ++ tailWord_776811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776815 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 3, 2, 2]
def baseStart_776815 : Nat := 118140960795 + 776815 * 2 ^ 59
def prefixEnd_776815 : Nat := 4983230072969 + 3 ^ 40 * 776815 * 2
def baseEnd_776815 : Nat := 398879474622483441439999

theorem tailTrace_776815 : CollatzResearch.WordTrace tailWord_776815 prefixEnd_776815 398879474622483441439999 := by
  unfold tailWord_776815
  simp only [CollatzResearch.WordTrace]
  refine ⟨28332770680739399284755899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18888513787159599523170599 28332770680739399284755899)
  ·
    refine ⟨42499156021109098927133849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28332770680739399284755899 42499156021109098927133849)
    ·
      refine ⟨31874367015831824195350387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42499156021109098927133849 31874367015831824195350387)
      ·
        refine ⟨47811550523747736293025581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31874367015831824195350387 47811550523747736293025581)
        ·
          refine ⟨17929331446405401109884593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47811550523747736293025581 17929331446405401109884593)
          ·
            refine ⟨13446998584804050832413445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17929331446405401109884593 13446998584804050832413445)
            ·
              refine ⟨2521312234650759531077521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13446998584804050832413445 2521312234650759531077521)
              ·
                refine ⟨1890984175988069648308141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521312234650759531077521 1890984175988069648308141)
                ·
                  refine ⟨709119065995526118115553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1890984175988069648308141 709119065995526118115553)
                  ·
                    refine ⟨531839299496644588586665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 709119065995526118115553 531839299496644588586665)
                    ·
                      refine ⟨398879474622483441439999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531839299496644588586665 398879474622483441439999)
                      ·
                        rfl

theorem cell23_776815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 2, 2].length) (baseStart_776815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776815 prefixEnd_776815 := by exact prefixLift 776815
  have htrace : WordTrace (prefixWord ++ tailWord_776815) baseStart_776815 baseEnd_776815 := by
    simpa [prefixWord, tailWord_776815, baseEnd_776815] using wordTrace_append hprefix tailTrace_776815
  have hstable : (prefixWord ++ tailWord_776815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776815).length < 2 ^ (prefixWord ++ tailWord_776815).sum := by decide
  have hdescent : baseEnd_776815 < baseStart_776815 := by decide
  rcases family_descends (prefixWord ++ tailWord_776815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776886 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_776886 : Nat := 118140960795 + 776886 * 2 ^ 59
def prefixEnd_776886 : Nat := 4983230072969 + 3 ^ 40 * 776886 * 2
def baseEnd_776886 : Nat := 398915931748952663652173

theorem tailTrace_776886 : CollatzResearch.WordTrace tailWord_776886 prefixEnd_776886 398915931748952663652173 := by
  unfold tailWord_776886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770960016467636150661907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18890240175654785607060341 1770960016467636150661907)
  ·
    refine ⟨2656440024701454225992861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1770960016467636150661907 2656440024701454225992861)
    ·
      refine ⟨996165009263045334747323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2656440024701454225992861 996165009263045334747323)
      ·
        refine ⟨1494247513894568002120985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996165009263045334747323 1494247513894568002120985)
        ·
          refine ⟨1120685635420926001590739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1494247513894568002120985 1120685635420926001590739)
          ·
            refine ⟨1681028453131389002386109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120685635420926001590739 1681028453131389002386109)
            ·
              refine ⟨630385669924270875894791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1681028453131389002386109 630385669924270875894791)
              ·
                refine ⟨945578504886406313842187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630385669924270875894791 945578504886406313842187)
                ·
                  refine ⟨1418367757329609470763281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945578504886406313842187 1418367757329609470763281)
                  ·
                    refine ⟨1063775817997207103072461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1418367757329609470763281 1063775817997207103072461)
                    ·
                      refine ⟨398915931748952663652173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1063775817997207103072461 398915931748952663652173)
                      ·
                        rfl

theorem cell23_776886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_776886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776886 prefixEnd_776886 := by exact prefixLift 776886
  have htrace : WordTrace (prefixWord ++ tailWord_776886) baseStart_776886 baseEnd_776886 := by
    simpa [prefixWord, tailWord_776886, baseEnd_776886] using wordTrace_append hprefix tailTrace_776886
  have hstable : (prefixWord ++ tailWord_776886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776886).length < 2 ^ (prefixWord ++ tailWord_776886).sum := by decide
  have hdescent : baseEnd_776886 < baseStart_776886 := by decide
  rcases family_descends (prefixWord ++ tailWord_776886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776922 : List Nat := [3, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2]
def baseStart_776922 : Nat := 118140960795 + 776922 * 2 ^ 59
def prefixEnd_776922 : Nat := 4983230072969 + 3 ^ 40 * 776922 * 2
def baseEnd_776922 : Nat := 398934417052514522802007

theorem tailTrace_776922 : CollatzResearch.WordTrace tailWord_776922 prefixEnd_776922 398934417052514522802007 := by
  unfold tailWord_776922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7084168322837939139725255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18891115527567837705934013 7084168322837939139725255)
  ·
    refine ⟨10626252484256908709587883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7084168322837939139725255 10626252484256908709587883)
    ·
      refine ⟨15939378726385363064381825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10626252484256908709587883 15939378726385363064381825)
      ·
        refine ⟨11954534044789022298286369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15939378726385363064381825 11954534044789022298286369)
        ·
          refine ⟨8965900533591766723714777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11954534044789022298286369 8965900533591766723714777)
          ·
            refine ⟨6724425400193825042786083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8965900533591766723714777 6724425400193825042786083)
            ·
              refine ⟨10086638100290737564179125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6724425400193825042786083 10086638100290737564179125)
              ·
                refine ⟨945622321902256646641793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10086638100290737564179125 945622321902256646641793)
                ·
                  refine ⟨709216741426692484981345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 945622321902256646641793 709216741426692484981345)
                  ·
                    refine ⟨531912556070019363736009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 709216741426692484981345 531912556070019363736009)
                    ·
                      refine ⟨398934417052514522802007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 531912556070019363736009 398934417052514522802007)
                      ·
                        rfl

theorem cell23_776922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2].length) (baseStart_776922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776922 prefixEnd_776922 := by exact prefixLift 776922
  have htrace : WordTrace (prefixWord ++ tailWord_776922) baseStart_776922 baseEnd_776922 := by
    simpa [prefixWord, tailWord_776922, baseEnd_776922] using wordTrace_append hprefix tailTrace_776922
  have hstable : (prefixWord ++ tailWord_776922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776922).length < 2 ^ (prefixWord ++ tailWord_776922).sum := by decide
  have hdescent : baseEnd_776922 < baseStart_776922 := by decide
  rcases family_descends (prefixWord ++ tailWord_776922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776938 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_776938 : Nat := 118140960795 + 776938 * 2 ^ 59
def prefixEnd_776938 : Nat := 4983230072969 + 3 ^ 40 * 776938 * 2
def baseEnd_776938 : Nat := 398942632742986460201933

theorem tailTrace_776938 : CollatzResearch.WordTrace tailWord_776938 prefixEnd_776938 398942632742986460201933 := by
  unfold tailWord_776938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7084314214823447822870867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18891504572862527527655645 7084314214823447822870867)
  ·
    refine ⟨10626471322235171734306301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7084314214823447822870867 10626471322235171734306301)
    ·
      refine ⟨3984926745838189400364863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10626471322235171734306301 3984926745838189400364863)
      ·
        refine ⟨5977390118757284100547295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3984926745838189400364863 5977390118757284100547295)
        ·
          refine ⟨8966085178135926150820943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5977390118757284100547295 8966085178135926150820943)
          ·
            refine ⟨13449127767203889226231415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8966085178135926150820943 13449127767203889226231415)
            ·
              refine ⟨20173691650805833839347123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13449127767203889226231415 20173691650805833839347123)
              ·
                refine ⟨30260537476208750759020685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20173691650805833839347123 30260537476208750759020685)
                ·
                  refine ⟨11347701553578281534632757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30260537476208750759020685 11347701553578281534632757)
                  ·
                    refine ⟨1063847020647963893871821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11347701553578281534632757 1063847020647963893871821)
                    ·
                      refine ⟨398942632742986460201933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1063847020647963893871821 398942632742986460201933)
                      ·
                        rfl

theorem cell23_776938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_776938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776938 prefixEnd_776938 := by exact prefixLift 776938
  have htrace : WordTrace (prefixWord ++ tailWord_776938) baseStart_776938 baseEnd_776938 := by
    simpa [prefixWord, tailWord_776938, baseEnd_776938] using wordTrace_append hprefix tailTrace_776938
  have hstable : (prefixWord ++ tailWord_776938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776938).length < 2 ^ (prefixWord ++ tailWord_776938).sum := by decide
  have hdescent : baseEnd_776938 < baseStart_776938 := by decide
  rcases family_descends (prefixWord ++ tailWord_776938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776945 : List Nat := [1, 2, 2, 2, 2, 2, 4, 3, 5]
def baseStart_776945 : Nat := 118140960795 + 776945 * 2 ^ 59
def prefixEnd_776945 : Nat := 4983230072969 + 3 ^ 40 * 776945 * 2
def baseEnd_776945 : Nat := 44327358567507548090489

theorem tailTrace_776945 : CollatzResearch.WordTrace tailWord_776945 prefixEnd_776945 44327358567507548090489 := by
  unfold tailWord_776945
  simp only [CollatzResearch.WordTrace]
  refine ⟨28337512170268431486988289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18891674780178954324658859 28337512170268431486988289)
  ·
    refine ⟨21253134127701323615241217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28337512170268431486988289 21253134127701323615241217)
    ·
      refine ⟨15939850595775992711430913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21253134127701323615241217 15939850595775992711430913)
      ·
        refine ⟨11954887946831994533573185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15939850595775992711430913 11954887946831994533573185)
        ·
          refine ⟨8966165960123995900179889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11954887946831994533573185 8966165960123995900179889)
          ·
            refine ⟨6724624470092996925134917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8966165960123995900179889 6724624470092996925134917)
            ·
              refine ⟨1260867088142436923462797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6724624470092996925134917 1260867088142436923462797)
              ·
                refine ⟨472825158053413846298549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1260867088142436923462797 472825158053413846298549)
                ·
                  refine ⟨44327358567507548090489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 472825158053413846298549 44327358567507548090489)
                  ·
                    rfl

theorem cell23_776945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 5].length) (baseStart_776945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776945 prefixEnd_776945 := by exact prefixLift 776945
  have htrace : WordTrace (prefixWord ++ tailWord_776945) baseStart_776945 baseEnd_776945 := by
    simpa [prefixWord, tailWord_776945, baseEnd_776945] using wordTrace_append hprefix tailTrace_776945
  have hstable : (prefixWord ++ tailWord_776945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776945).length < 2 ^ (prefixWord ++ tailWord_776945).sum := by decide
  have hdescent : baseEnd_776945 < baseStart_776945 := by decide
  rcases family_descends (prefixWord ++ tailWord_776945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_776962 : List Nat := [3, 4, 1, 1, 1, 2, 2, 4, 5]
def baseStart_776962 : Nat := 118140960795 + 776962 * 2 ^ 59
def prefixEnd_776962 : Nat := 4983230072969 + 3 ^ 40 * 776962 * 2
def baseEnd_776962 : Nat := 44328328475410485144647

theorem tailTrace_776962 : CollatzResearch.WordTrace tailWord_776962 prefixEnd_776962 44328328475410485144647 := by
  unfold tailWord_776962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7084533052801710847589285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18892088140804562260238093 7084533052801710847589285)
  ·
    refine ⟨1328349947400320783922991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7084533052801710847589285 1328349947400320783922991)
    ·
      refine ⟨1992524921100481175884487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1328349947400320783922991 1992524921100481175884487)
      ·
        refine ⟨2988787381650721763826731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992524921100481175884487 2988787381650721763826731)
        ·
          refine ⟨4483181072476082645740097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2988787381650721763826731 4483181072476082645740097)
          ·
            refine ⟨3362385804357061984305073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4483181072476082645740097 3362385804357061984305073)
            ·
              refine ⟨2521789353267796488228805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3362385804357061984305073 2521789353267796488228805)
              ·
                refine ⟨472835503737711841542901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2521789353267796488228805 472835503737711841542901)
                ·
                  refine ⟨44328328475410485144647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 472835503737711841542901 44328328475410485144647)
                  ·
                    rfl

theorem cell23_776962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_776962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_776962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_776962 prefixEnd_776962 := by exact prefixLift 776962
  have htrace : WordTrace (prefixWord ++ tailWord_776962) baseStart_776962 baseEnd_776962 := by
    simpa [prefixWord, tailWord_776962, baseEnd_776962] using wordTrace_append hprefix tailTrace_776962
  have hstable : (prefixWord ++ tailWord_776962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_776962).length < 2 ^ (prefixWord ++ tailWord_776962).sum := by decide
  have hdescent : baseEnd_776962 < baseStart_776962 := by decide
  rcases family_descends (prefixWord ++ tailWord_776962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777015 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_777015 : Nat := 118140960795 + 777015 * 2 ^ 59
def prefixEnd_777015 : Nat := 4983230072969 + 3 ^ 40 * 777015 * 2
def baseEnd_777015 : Nat := 398982170753382658939079

theorem tailTrace_777015 : CollatzResearch.WordTrace tailWord_777015 prefixEnd_777015 398982170753382658939079 := by
  unfold tailWord_777015
  simp only [CollatzResearch.WordTrace]
  refine ⟨28340065280014833442036499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18893376853343222294690999 28340065280014833442036499)
  ·
    refine ⟨42510097920022250163054749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28340065280014833442036499 42510097920022250163054749)
    ·
      refine ⟨15941286720008343811145531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42510097920022250163054749 15941286720008343811145531)
      ·
        refine ⟨23911930080012515716718297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15941286720008343811145531 23911930080012515716718297)
        ·
          refine ⟨17933947560009386787538723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23911930080012515716718297 17933947560009386787538723)
          ·
            refine ⟨26900921340014080181308085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17933947560009386787538723 26900921340014080181308085)
            ·
              refine ⟨2521961375626320016997633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26900921340014080181308085 2521961375626320016997633)
              ·
                refine ⟨1891471031719740012748225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521961375626320016997633 1891471031719740012748225)
                ·
                  refine ⟨1418603273789805009561169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1891471031719740012748225 1418603273789805009561169)
                  ·
                    refine ⟨1063952455342353757170877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1418603273789805009561169 1063952455342353757170877)
                    ·
                      refine ⟨398982170753382658939079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1063952455342353757170877 398982170753382658939079)
                      ·
                        rfl

theorem cell23_777015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_777015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777015 prefixEnd_777015 := by exact prefixLift 777015
  have htrace : WordTrace (prefixWord ++ tailWord_777015) baseStart_777015 baseEnd_777015 := by
    simpa [prefixWord, tailWord_777015, baseEnd_777015] using wordTrace_append hprefix tailTrace_777015
  have hstable : (prefixWord ++ tailWord_777015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777015).length < 2 ^ (prefixWord ++ tailWord_777015).sum := by decide
  have hdescent : baseEnd_777015 < baseStart_777015 := by decide
  rcases family_descends (prefixWord ++ tailWord_777015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777038 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_777038 : Nat := 118140960795 + 777038 * 2 ^ 59
def prefixEnd_777038 : Nat := 4983230072969 + 3 ^ 40 * 777038 * 2
def baseEnd_777038 : Nat := 398993980808436068951473

theorem tailTrace_777038 : CollatzResearch.WordTrace tailWord_777038 prefixEnd_777038 398993980808436068951473 := by
  unfold tailWord_777038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3542613019866438546265471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18893936105954338913415845 3542613019866438546265471)
  ·
    refine ⟨5313919529799657819398207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3542613019866438546265471 5313919529799657819398207)
    ·
      refine ⟨7970879294699486729097311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5313919529799657819398207 7970879294699486729097311)
      ·
        refine ⟨11956318942049230093645967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7970879294699486729097311 11956318942049230093645967)
        ·
          refine ⟨17934478413073845140468951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11956318942049230093645967 17934478413073845140468951)
          ·
            refine ⟨26901717619610767710703427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17934478413073845140468951 26901717619610767710703427)
            ·
              refine ⟨40352576429416151566055141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26901717619610767710703427 40352576429416151566055141)
              ·
                refine ⟨7566108080515528418635339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40352576429416151566055141 7566108080515528418635339)
                ·
                  refine ⟨11349162120773292627953009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7566108080515528418635339 11349162120773292627953009)
                  ·
                    refine ⟨8511871590579969470964757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11349162120773292627953009 8511871590579969470964757)
                    ·
                      refine ⟨398993980808436068951473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8511871590579969470964757 398993980808436068951473)
                      ·
                        rfl

theorem cell23_777038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_777038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777038 prefixEnd_777038 := by exact prefixLift 777038
  have htrace : WordTrace (prefixWord ++ tailWord_777038) baseStart_777038 baseEnd_777038 := by
    simpa [prefixWord, tailWord_777038, baseEnd_777038] using wordTrace_append hprefix tailTrace_777038
  have hstable : (prefixWord ++ tailWord_777038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777038).length < 2 ^ (prefixWord ++ tailWord_777038).sum := by decide
  have hdescent : baseEnd_777038 < baseStart_777038 := by decide
  rcases family_descends (prefixWord ++ tailWord_777038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777072 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 2, 3, 2]
def baseStart_777072 : Nat := 118140960795 + 777072 * 2 ^ 59
def prefixEnd_777072 : Nat := 4983230072969 + 3 ^ 40 * 777072 * 2
def baseEnd_777072 : Nat := 399011439150688935926317

theorem tailTrace_777072 : CollatzResearch.WordTrace tailWord_777072 prefixEnd_777072 399011439150688935926317 := by
  unfold tailWord_777072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14171072120404166088430735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18894762827205554784574313 14171072120404166088430735)
  ·
    refine ⟨21256608180606249132646103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14171072120404166088430735 21256608180606249132646103)
    ·
      refine ⟨31884912270909373698969155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21256608180606249132646103 31884912270909373698969155)
      ·
        refine ⟨47827368406364060548453733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31884912270909373698969155 47827368406364060548453733)
        ·
          refine ⟨8967631576193261352835075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47827368406364060548453733 8967631576193261352835075)
          ·
            refine ⟨13451447364289892029252613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8967631576193261352835075 13451447364289892029252613)
            ·
              refine ⟨2522146380804354755484865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13451447364289892029252613 2522146380804354755484865)
              ·
                refine ⟨1891609785603266066613649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2522146380804354755484865 1891609785603266066613649)
                ·
                  refine ⟨1418707339202449549960237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1891609785603266066613649 1418707339202449549960237)
                  ·
                    refine ⟨532015252200918581235089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1418707339202449549960237 532015252200918581235089)
                    ·
                      refine ⟨399011439150688935926317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532015252200918581235089 399011439150688935926317)
                      ·
                        rfl

theorem cell23_777072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 3, 2].length) (baseStart_777072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777072 prefixEnd_777072 := by exact prefixLift 777072
  have htrace : WordTrace (prefixWord ++ tailWord_777072) baseStart_777072 baseEnd_777072 := by
    simpa [prefixWord, tailWord_777072, baseEnd_777072] using wordTrace_append hprefix tailTrace_777072
  have hstable : (prefixWord ++ tailWord_777072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777072).length < 2 ^ (prefixWord ++ tailWord_777072).sum := by decide
  have hdescent : baseEnd_777072 < baseStart_777072 := by decide
  rcases family_descends (prefixWord ++ tailWord_777072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777085 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_777085 : Nat := 118140960795 + 777085 * 2 ^ 59
def prefixEnd_777085 : Nat := 4983230072969 + 3 ^ 40 * 777085 * 2
def baseEnd_777085 : Nat := 399018114399197385063757

theorem tailTrace_777085 : CollatzResearch.WordTrace tailWord_777085 prefixEnd_777085 399018114399197385063757 := by
  unfold tailWord_777085
  simp only [CollatzResearch.WordTrace]
  refine ⟨28342618389761235397084709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18895078926507490264723139 28342618389761235397084709)
  ·
    refine ⟨5314240948080231636953383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28342618389761235397084709 5314240948080231636953383)
    ·
      refine ⟨7971361422120347455430075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314240948080231636953383 7971361422120347455430075)
      ·
        refine ⟨11957042133180521183145113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7971361422120347455430075 11957042133180521183145113)
        ·
          refine ⟨8967781599885390887358835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11957042133180521183145113 8967781599885390887358835)
          ·
            refine ⟨13451672399828086331038253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8967781599885390887358835 13451672399828086331038253)
            ·
              refine ⟨5044377149935532374139345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13451672399828086331038253 5044377149935532374139345)
              ·
                refine ⟨3783282862451649280604509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5044377149935532374139345 3783282862451649280604509)
                ·
                  refine ⟨1418731073419368480226691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3783282862451649280604509 1418731073419368480226691)
                  ·
                    refine ⟨2128096610129052720340037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1418731073419368480226691 2128096610129052720340037)
                    ·
                      refine ⟨399018114399197385063757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2128096610129052720340037 399018114399197385063757)
                      ·
                        rfl

theorem cell23_777085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_777085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777085 prefixEnd_777085 := by exact prefixLift 777085
  have htrace : WordTrace (prefixWord ++ tailWord_777085) baseStart_777085 baseEnd_777085 := by
    simpa [prefixWord, tailWord_777085, baseEnd_777085] using wordTrace_append hprefix tailTrace_777085
  have hstable : (prefixWord ++ tailWord_777085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777085).length < 2 ^ (prefixWord ++ tailWord_777085).sum := by decide
  have hdescent : baseEnd_777085 < baseStart_777085 := by decide
  rcases family_descends (prefixWord ++ tailWord_777085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777095 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 1, 6]
def baseStart_777095 : Nat := 118140960795 + 777095 * 2 ^ 59
def prefixEnd_777095 : Nat := 4983230072969 + 3 ^ 40 * 777095 * 2
def baseEnd_777095 : Nat := 133007749735247448646237

theorem tailTrace_777095 : CollatzResearch.WordTrace tailWord_777095 prefixEnd_777095 133007749735247448646237 := by
  unfold tailWord_777095
  simp only [CollatzResearch.WordTrace]
  refine ⟨28342983119725007104948739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18895322079816671403299159 28342983119725007104948739)
  ·
    refine ⟨42514474679587510657423109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28342983119725007104948739 42514474679587510657423109)
    ·
      refine ⟨7971464002422658248266833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42514474679587510657423109 7971464002422658248266833)
      ·
        refine ⟨5978598001816993686200125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7971464002422658248266833 5978598001816993686200125)
        ·
          refine ⟨2241974250681372632325047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5978598001816993686200125 2241974250681372632325047)
          ·
            refine ⟨3362961376022058948487571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241974250681372632325047 3362961376022058948487571)
            ·
              refine ⟨5044442064033088422731357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3362961376022058948487571 5044442064033088422731357)
              ·
                refine ⟨1891665774012408158524259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5044442064033088422731357 1891665774012408158524259)
                ·
                  refine ⟨2837498661018612237786389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891665774012408158524259 2837498661018612237786389)
                  ·
                    refine ⟨133007749735247448646237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2837498661018612237786389 133007749735247448646237)
                    ·
                      rfl

theorem cell23_777095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_777095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777095 prefixEnd_777095 := by exact prefixLift 777095
  have htrace : WordTrace (prefixWord ++ tailWord_777095) baseStart_777095 baseEnd_777095 := by
    simpa [prefixWord, tailWord_777095, baseEnd_777095] using wordTrace_append hprefix tailTrace_777095
  have hstable : (prefixWord ++ tailWord_777095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777095).length < 2 ^ (prefixWord ++ tailWord_777095).sum := by decide
  have hdescent : baseEnd_777095 < baseStart_777095 := by decide
  rcases family_descends (prefixWord ++ tailWord_777095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777116 : List Nat := [2, 2, 3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_777116 : Nat := 118140960795 + 777116 * 2 ^ 59
def prefixEnd_777116 : Nat := 4983230072969 + 3 ^ 40 * 777116 * 2
def baseEnd_777116 : Nat := 133011344099828921258705

theorem tailTrace_777116 : CollatzResearch.WordTrace tailWord_777116 prefixEnd_777116 133011344099828921258705 := by
  unfold tailWord_777116
  simp only [CollatzResearch.WordTrace]
  refine ⟨14171874526324463845731601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18895832701765951794308801 14171874526324463845731601)
  ·
    refine ⟨10628905894743347884298701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14171874526324463845731601 10628905894743347884298701)
    ·
      refine ⟨3985839710528755456612013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10628905894743347884298701 3985839710528755456612013)
      ·
        refine ⟨1494689891448283296229505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3985839710528755456612013 1494689891448283296229505)
        ·
          refine ⟨1121017418586212472172129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1494689891448283296229505 1121017418586212472172129)
          ·
            refine ⟨840763063939659354129097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121017418586212472172129 840763063939659354129097)
            ·
              refine ⟨630572297954744515596823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840763063939659354129097 630572297954744515596823)
              ·
                refine ⟨945858446932116773395235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630572297954744515596823 945858446932116773395235)
                ·
                  refine ⟨1418787670398175160092853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945858446932116773395235 1418787670398175160092853)
                  ·
                    refine ⟨133011344099828921258705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1418787670398175160092853 133011344099828921258705)
                    ·
                      rfl

theorem cell23_777116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_777116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777116 prefixEnd_777116 := by exact prefixLift 777116
  have htrace : WordTrace (prefixWord ++ tailWord_777116) baseStart_777116 baseEnd_777116 := by
    simpa [prefixWord, tailWord_777116, baseEnd_777116] using wordTrace_append hprefix tailTrace_777116
  have hstable : (prefixWord ++ tailWord_777116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777116).length < 2 ^ (prefixWord ++ tailWord_777116).sum := by decide
  have hdescent : baseEnd_777116 < baseStart_777116 := by decide
  rcases family_descends (prefixWord ++ tailWord_777116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777119 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 1, 1, 4]
def baseStart_777119 : Nat := 118140960795 + 777119 * 2 ^ 59
def prefixEnd_777119 : Nat := 4983230072969 + 3 ^ 40 * 777119 * 2
def baseEnd_777119 : Nat := 399035572741450252038601

theorem tailTrace_777119 : CollatzResearch.WordTrace tailWord_777119 prefixEnd_777119 399035572741450252038601 := by
  unfold tailWord_777119
  simp only [CollatzResearch.WordTrace]
  refine ⟨28343858471638059203822411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18895905647758706135881607 28343858471638059203822411)
  ·
    refine ⟨42515787707457088805733617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28343858471638059203822411 42515787707457088805733617)
    ·
      refine ⟨31886840780592816604300213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42515787707457088805733617 31886840780592816604300213)
      ·
        refine ⟨2989391323180576556653145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31886840780592816604300213 2989391323180576556653145)
        ·
          refine ⟨2242043492385432417489859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2989391323180576556653145 2242043492385432417489859)
          ·
            refine ⟨3363065238578148626234789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242043492385432417489859 3363065238578148626234789)
            ·
              refine ⟨630574732233402867419023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3363065238578148626234789 630574732233402867419023)
              ·
                refine ⟨945862098350104301128535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630574732233402867419023 945862098350104301128535)
                ·
                  refine ⟨1418793147525156451692803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945862098350104301128535 1418793147525156451692803)
                  ·
                    refine ⟨2128189721287734677539205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1418793147525156451692803 2128189721287734677539205)
                    ·
                      refine ⟨399035572741450252038601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2128189721287734677539205 399035572741450252038601)
                      ·
                        rfl

theorem cell23_777119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_777119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777119 prefixEnd_777119 := by exact prefixLift 777119
  have htrace : WordTrace (prefixWord ++ tailWord_777119) baseStart_777119 baseEnd_777119 := by
    simpa [prefixWord, tailWord_777119, baseEnd_777119] using wordTrace_append hprefix tailTrace_777119
  have hstable : (prefixWord ++ tailWord_777119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777119).length < 2 ^ (prefixWord ++ tailWord_777119).sum := by decide
  have hdescent : baseEnd_777119 < baseStart_777119 := by decide
  rcases family_descends (prefixWord ++ tailWord_777119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777149 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_777149 : Nat := 118140960795 + 777149 * 2 ^ 59
def prefixEnd_777149 : Nat := 4983230072969 + 3 ^ 40 * 777149 * 2
def baseEnd_777149 : Nat := 399050977161085134663463

theorem tailTrace_777149 : CollatzResearch.WordTrace tailWord_777149 prefixEnd_777149 399050977161085134663463 := by
  unfold tailWord_777149
  simp only [CollatzResearch.WordTrace]
  refine ⟨28344952661529374327414501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18896635107686249551609667 28344952661529374327414501)
  ·
    refine ⟨5314678624036757686390219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28344952661529374327414501 5314678624036757686390219)
    ·
      refine ⟨7972017936055136529585329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314678624036757686390219 7972017936055136529585329)
      ·
        refine ⟨5979013452041352397188997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7972017936055136529585329 5979013452041352397188997)
        ·
          refine ⟨1121065022257753574472937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5979013452041352397188997 1121065022257753574472937)
          ·
            refine ⟨840798766693315180854703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1121065022257753574472937 840798766693315180854703)
            ·
              refine ⟨1261198150039972771282055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840798766693315180854703 1261198150039972771282055)
              ·
                refine ⟨1891797225059959156923083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261198150039972771282055 1891797225059959156923083)
                ·
                  refine ⟨2837695837589938735384625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891797225059959156923083 2837695837589938735384625)
                  ·
                    refine ⟨2128271878192454051538469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2837695837589938735384625 2128271878192454051538469)
                    ·
                      refine ⟨399050977161085134663463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2128271878192454051538469 399050977161085134663463)
                      ·
                        rfl

theorem cell23_777149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_777149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777149 prefixEnd_777149 := by exact prefixLift 777149
  have htrace : WordTrace (prefixWord ++ tailWord_777149) baseStart_777149 baseEnd_777149 := by
    simpa [prefixWord, tailWord_777149, baseEnd_777149] using wordTrace_append hprefix tailTrace_777149
  have hstable : (prefixWord ++ tailWord_777149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777149).length < 2 ^ (prefixWord ++ tailWord_777149).sum := by decide
  have hdescent : baseEnd_777149 < baseStart_777149 := by decide
  rcases family_descends (prefixWord ++ tailWord_777149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777152 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 3]
def baseStart_777152 : Nat := 118140960795 + 777152 * 2 ^ 59
def prefixEnd_777152 : Nat := 4983230072969 + 3 ^ 40 * 777152 * 2
def baseEnd_777152 : Nat := 399052517603048622925949

theorem tailTrace_777152 : CollatzResearch.WordTrace tailWord_777152 prefixEnd_777152 399052517603048622925949 := by
  unfold tailWord_777152
  simp only [CollatzResearch.WordTrace]
  refine ⟨14172531040259252919886855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18896708053679003893182473 14172531040259252919886855)
  ·
    refine ⟨21258796560388879379830283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14172531040259252919886855 21258796560388879379830283)
    ·
      refine ⟨31888194840583319069745425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21258796560388879379830283 31888194840583319069745425)
      ·
        refine ⟨23916146130437489302309069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31888194840583319069745425 23916146130437489302309069)
        ·
          refine ⟨8968554798914058488365901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23916146130437489302309069 8968554798914058488365901)
          ·
            refine ⟨3363208049592771933137213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8968554798914058488365901 3363208049592771933137213)
            ·
              refine ⟨1261203018597289474926455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3363208049592771933137213 1261203018597289474926455)
              ·
                refine ⟨1891804527895934212389683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261203018597289474926455 1891804527895934212389683)
                ·
                  refine ⟨2837706791843901318584525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1891804527895934212389683 2837706791843901318584525)
                  ·
                    refine ⟨1064140046941462994469197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2837706791843901318584525 1064140046941462994469197)
                    ·
                      refine ⟨399052517603048622925949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1064140046941462994469197 399052517603048622925949)
                      ·
                        rfl

theorem cell23_777152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_777152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777152 prefixEnd_777152 := by exact prefixLift 777152
  have htrace : WordTrace (prefixWord ++ tailWord_777152) baseStart_777152 baseEnd_777152 := by
    simpa [prefixWord, tailWord_777152, baseEnd_777152] using wordTrace_append hprefix tailTrace_777152
  have hstable : (prefixWord ++ tailWord_777152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777152).length < 2 ^ (prefixWord ++ tailWord_777152).sum := by decide
  have hdescent : baseEnd_777152 < baseStart_777152 := by decide
  rcases family_descends (prefixWord ++ tailWord_777152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777170 : List Nat := [3, 2, 2, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_777170 : Nat := 118140960795 + 777170 * 2 ^ 59
def prefixEnd_777170 : Nat := 4983230072969 + 3 ^ 40 * 777170 * 2
def baseEnd_777170 : Nat := 399061760254829552500867

theorem tailTrace_777170 : CollatzResearch.WordTrace tailWord_777170 prefixEnd_777170 399061760254829552500867 := by
  unfold tailWord_777170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086429648613323728482241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18897145729635529942619309 7086429648613323728482241)
  ·
    refine ⟨5314822236459992796361681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7086429648613323728482241 5314822236459992796361681)
    ·
      refine ⟨3986116677344994597271261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5314822236459992796361681 3986116677344994597271261)
      ·
        refine ⟨1494793754004372973976723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3986116677344994597271261 1494793754004372973976723)
        ·
          refine ⟨2242190631006559460965085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494793754004372973976723 2242190631006559460965085)
          ·
            refine ⟨840821486627459797861907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2242190631006559460965085 840821486627459797861907)
            ·
              refine ⟨1261232229941189696792861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840821486627459797861907 1261232229941189696792861)
              ·
                refine ⟨472962086227946136297323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1261232229941189696792861 472962086227946136297323)
                ·
                  refine ⟨709443129341919204445985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472962086227946136297323 709443129341919204445985)
                  ·
                    refine ⟨532082347006439403334489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 709443129341919204445985 532082347006439403334489)
                    ·
                      refine ⟨399061760254829552500867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532082347006439403334489 399061760254829552500867)
                      ·
                        rfl

theorem cell23_777170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_777170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777170 prefixEnd_777170 := by exact prefixLift 777170
  have htrace : WordTrace (prefixWord ++ tailWord_777170) baseStart_777170 baseEnd_777170 := by
    simpa [prefixWord, tailWord_777170, baseEnd_777170] using wordTrace_append hprefix tailTrace_777170
  have hstable : (prefixWord ++ tailWord_777170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777170).length < 2 ^ (prefixWord ++ tailWord_777170).sum := by decide
  have hdescent : baseEnd_777170 < baseStart_777170 := by decide
  rcases family_descends (prefixWord ++ tailWord_777170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777186 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_777186 : Nat := 118140960795 + 777186 * 2 ^ 59
def prefixEnd_777186 : Nat := 4983230072969 + 3 ^ 40 * 777186 * 2
def baseEnd_777186 : Nat := 399069975945301489900793

theorem tailTrace_777186 : CollatzResearch.WordTrace tailWord_777186 prefixEnd_777186 399069975945301489900793 := by
  unfold tailWord_777186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086575540598832411627853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18897534774930219764340941 7086575540598832411627853)
  ·
    refine ⟨2657465827724562154360445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7086575540598832411627853 2657465827724562154360445)
    ·
      refine ⟨996549685396710807885167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2657465827724562154360445 996549685396710807885167)
      ·
        refine ⟨1494824528095066211827751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996549685396710807885167 1494824528095066211827751)
        ·
          refine ⟨2242236792142599317741627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494824528095066211827751 2242236792142599317741627)
          ·
            refine ⟨3363355188213898976612441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242236792142599317741627 3363355188213898976612441)
            ·
              refine ⟨2522516391160424232459331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3363355188213898976612441 2522516391160424232459331)
              ·
                refine ⟨3783774586740636348688997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2522516391160424232459331 3783774586740636348688997)
                ·
                  refine ⟨709457735013869315379187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3783774586740636348688997 709457735013869315379187)
                  ·
                    refine ⟨1064186602520803973068781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 709457735013869315379187 1064186602520803973068781)
                    ·
                      refine ⟨399069975945301489900793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1064186602520803973068781 399069975945301489900793)
                      ·
                        rfl

theorem cell23_777186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_777186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777186 prefixEnd_777186 := by exact prefixLift 777186
  have htrace : WordTrace (prefixWord ++ tailWord_777186) baseStart_777186 baseEnd_777186 := by
    simpa [prefixWord, tailWord_777186, baseEnd_777186] using wordTrace_append hprefix tailTrace_777186
  have hstable : (prefixWord ++ tailWord_777186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777186).length < 2 ^ (prefixWord ++ tailWord_777186).sum := by decide
  have hdescent : baseEnd_777186 < baseStart_777186 := by decide
  rcases family_descends (prefixWord ++ tailWord_777186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777242 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3]
def baseStart_777242 : Nat := 118140960795 + 777242 * 2 ^ 59
def prefixEnd_777242 : Nat := 4983230072969 + 3 ^ 40 * 777242 * 2
def baseEnd_777242 : Nat := 399098730861953270800535

theorem tailTrace_777242 : CollatzResearch.WordTrace tailWord_777242 prefixEnd_777242 399098730861953270800535 := by
  unfold tailWord_777242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7087086162548112802637495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18898896433461634140366653 7087086162548112802637495)
  ·
    refine ⟨10630629243822169203956243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7087086162548112802637495 10630629243822169203956243)
    ·
      refine ⟨15945943865733253805934365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10630629243822169203956243 15945943865733253805934365)
      ·
        refine ⟨5979728949649970177225387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15945943865733253805934365 5979728949649970177225387)
        ·
          refine ⟨8969593424474955265838081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5979728949649970177225387 8969593424474955265838081)
          ·
            refine ⟨6727195068356216449378561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8969593424474955265838081 6727195068356216449378561)
            ·
              refine ⟨5045396301267162337033921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6727195068356216449378561 5045396301267162337033921)
              ·
                refine ⟨3784047225950371752775441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045396301267162337033921 3784047225950371752775441)
                ·
                  refine ⟨2838035419462778814581581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3784047225950371752775441 2838035419462778814581581)
                  ·
                    refine ⟨1064263282298542055468093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838035419462778814581581 1064263282298542055468093)
                    ·
                      refine ⟨399098730861953270800535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1064263282298542055468093 399098730861953270800535)
                      ·
                        rfl

theorem cell23_777242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_777242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777242 prefixEnd_777242 := by exact prefixLift 777242
  have htrace : WordTrace (prefixWord ++ tailWord_777242) baseStart_777242 baseEnd_777242 := by
    simpa [prefixWord, tailWord_777242, baseEnd_777242] using wordTrace_append hprefix tailTrace_777242
  have hstable : (prefixWord ++ tailWord_777242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777242).length < 2 ^ (prefixWord ++ tailWord_777242).sum := by decide
  have hdescent : baseEnd_777242 < baseStart_777242 := by decide
  rcases family_descends (prefixWord ++ tailWord_777242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777249 : List Nat := [1, 2, 3, 2, 3, 2, 1, 4, 5]
def baseStart_777249 : Nat := 118140960795 + 777249 * 2 ^ 59
def prefixEnd_777249 : Nat := 4983230072969 + 3 ^ 40 * 777249 * 2
def baseEnd_777249 : Nat := 44344702802948304823667

theorem tailTrace_777249 : CollatzResearch.WordTrace tailWord_777249 prefixEnd_777249 44344702802948304823667 := by
  unfold tailWord_777249
  simp only [CollatzResearch.WordTrace]
  refine ⟨28348599961167091406054801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18899066640778060937369867 28348599961167091406054801)
  ·
    refine ⟨21261449970875318554541101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28348599961167091406054801 21261449970875318554541101)
    ·
      refine ⟨7973043739078244457952913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21261449970875318554541101 7973043739078244457952913)
      ·
        refine ⟨5979782804308683343464685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7973043739078244457952913 5979782804308683343464685)
        ·
          refine ⟨2242418551615756253799257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5979782804308683343464685 2242418551615756253799257)
          ·
            refine ⟨1681813913711817190349443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242418551615756253799257 1681813913711817190349443)
            ·
              refine ⟨2522720870567725785524165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1681813913711817190349443 2522720870567725785524165)
              ·
                refine ⟨473010163231448584785781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2522720870567725785524165 473010163231448584785781)
                ·
                  refine ⟨44344702802948304823667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 473010163231448584785781 44344702802948304823667)
                  ·
                    rfl

theorem cell23_777249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 5].length) (baseStart_777249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777249 prefixEnd_777249 := by exact prefixLift 777249
  have htrace : WordTrace (prefixWord ++ tailWord_777249) baseStart_777249 baseEnd_777249 := by
    simpa [prefixWord, tailWord_777249, baseEnd_777249] using wordTrace_append hprefix tailTrace_777249
  have hstable : (prefixWord ++ tailWord_777249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777249).length < 2 ^ (prefixWord ++ tailWord_777249).sum := by decide
  have hdescent : baseEnd_777249 < baseStart_777249 := by decide
  rcases family_descends (prefixWord ++ tailWord_777249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777262 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_777262 : Nat := 118140960795 + 777262 * 2 ^ 59
def prefixEnd_777262 : Nat := 4983230072969 + 3 ^ 40 * 777262 * 2
def baseEnd_777262 : Nat := 133036333491681064183481

theorem tailTrace_777262 : CollatzResearch.WordTrace tailWord_777262 prefixEnd_777262 133036333491681064183481 := by
  unfold tailWord_777262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3543634263764999328284755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18899382740079996417518693 3543634263764999328284755)
  ·
    refine ⟨5315451395647498992427133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3543634263764999328284755 5315451395647498992427133)
    ·
      refine ⟨1993294273367812122160175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5315451395647498992427133 1993294273367812122160175)
      ·
        refine ⟨2989941410051718183240263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993294273367812122160175 2989941410051718183240263)
        ·
          refine ⟨4484912115077577274860395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989941410051718183240263 4484912115077577274860395)
          ·
            refine ⟨6727368172616365912290593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4484912115077577274860395 6727368172616365912290593)
            ·
              refine ⟨5045526129462274434217945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6727368172616365912290593 5045526129462274434217945)
              ·
                refine ⟨3784144597096705825663459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5045526129462274434217945 3784144597096705825663459)
                ·
                  refine ⟨5676216895645058738495189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3784144597096705825663459 5676216895645058738495189)
                  ·
                    refine ⟨133036333491681064183481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5676216895645058738495189 133036333491681064183481)
                    ·
                      rfl

theorem cell23_777262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_777262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777262 prefixEnd_777262 := by exact prefixLift 777262
  have htrace : WordTrace (prefixWord ++ tailWord_777262) baseStart_777262 baseEnd_777262 := by
    simpa [prefixWord, tailWord_777262, baseEnd_777262] using wordTrace_append hprefix tailTrace_777262
  have hstable : (prefixWord ++ tailWord_777262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777262).length < 2 ^ (prefixWord ++ tailWord_777262).sum := by decide
  have hdescent : baseEnd_777262 < baseStart_777262 := by decide
  rcases family_descends (prefixWord ++ tailWord_777262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777292 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_777292 : Nat := 118140960795 + 777292 * 2 ^ 59
def prefixEnd_777292 : Nat := 4983230072969 + 3 ^ 40 * 777292 * 2
def baseEnd_777292 : Nat := 133041468298226025058435

theorem tailTrace_777292 : CollatzResearch.WordTrace tailWord_777292 prefixEnd_777292 133041468298226025058435 := by
  unfold tailWord_777292
  simp only [CollatzResearch.WordTrace]
  refine ⟨14175084150005654874935065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18900112200007539833246753 14175084150005654874935065)
  ·
    refine ⟨10631313112504241156201299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14175084150005654874935065 10631313112504241156201299)
    ·
      refine ⟨15946969668756361734301949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10631313112504241156201299 15946969668756361734301949)
      ·
        refine ⟨5980113625783635650363231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15946969668756361734301949 5980113625783635650363231)
        ·
          refine ⟨8970170438675453475544847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5980113625783635650363231 8970170438675453475544847)
          ·
            refine ⟨13455255658013180213317271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8970170438675453475544847 13455255658013180213317271)
            ·
              refine ⟨20182883487019770319975907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13455255658013180213317271 20182883487019770319975907)
              ·
                refine ⟨30274325230529655479963861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20182883487019770319975907 30274325230529655479963861)
                ·
                  refine ⟨709554497590538800311653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 30274325230529655479963861 709554497590538800311653)
                  ·
                    refine ⟨133041468298226025058435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 709554497590538800311653 133041468298226025058435)
                    ·
                      rfl

theorem cell23_777292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_777292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777292 prefixEnd_777292 := by exact prefixLift 777292
  have htrace : WordTrace (prefixWord ++ tailWord_777292) baseStart_777292 baseEnd_777292 := by
    simpa [prefixWord, tailWord_777292, baseEnd_777292] using wordTrace_append hprefix tailTrace_777292
  have hstable : (prefixWord ++ tailWord_777292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777292).length < 2 ^ (prefixWord ++ tailWord_777292).sum := by decide
  have hdescent : baseEnd_777292 < baseStart_777292 := by decide
  rcases family_descends (prefixWord ++ tailWord_777292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777386 : List Nat := [3, 1, 5, 1, 1, 2, 1, 1, 3, 5]
def baseStart_777386 : Nat := 118140960795 + 777386 * 2 ^ 59
def prefixEnd_777386 : Nat := 4983230072969 + 3 ^ 40 * 777386 * 2
def baseEnd_777386 : Nat := 133057557358733569133291

theorem tailTrace_777386 : CollatzResearch.WordTrace tailWord_777386 prefixEnd_777386 133057557358733569133291 := by
  unfold tailWord_777386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088399190417690950948003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18902397841113842535861341 7088399190417690950948003)
  ·
    refine ⟨10632598785626536426422005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7088399190417690950948003 10632598785626536426422005)
    ·
      refine ⟨996806136152487789977063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10632598785626536426422005 996806136152487789977063)
      ·
        refine ⟨1495209204228731684965595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996806136152487789977063 1495209204228731684965595)
        ·
          refine ⟨2242813806343097527448393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495209204228731684965595 2242813806343097527448393)
          ·
            refine ⟨1682110354757323145586295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242813806343097527448393 1682110354757323145586295)
            ·
              refine ⟨2523165532135984718379443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682110354757323145586295 2523165532135984718379443)
              ·
                refine ⟨3784748298203977077569165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2523165532135984718379443 3784748298203977077569165)
                ·
                  refine ⟨1419280611826491404088437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3784748298203977077569165 1419280611826491404088437)
                  ·
                    refine ⟨133057557358733569133291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1419280611826491404088437 133057557358733569133291)
                    ·
                      rfl

theorem cell23_777386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_777386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777386 prefixEnd_777386 := by exact prefixLift 777386
  have htrace : WordTrace (prefixWord ++ tailWord_777386) baseStart_777386 baseEnd_777386 := by
    simpa [prefixWord, tailWord_777386, baseEnd_777386] using wordTrace_append hprefix tailTrace_777386
  have hstable : (prefixWord ++ tailWord_777386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777386).length < 2 ^ (prefixWord ++ tailWord_777386).sum := by decide
  have hdescent : baseEnd_777386 < baseStart_777386 := by decide
  rcases family_descends (prefixWord ++ tailWord_777386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777392 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 3]
def baseStart_777392 : Nat := 118140960795 + 777392 * 2 ^ 59
def prefixEnd_777392 : Nat := 4983230072969 + 3 ^ 40 * 777392 * 2
def baseEnd_777392 : Nat := 399175752960127683924845

theorem tailTrace_777392 : CollatzResearch.WordTrace tailWord_777392 prefixEnd_777392 399175752960127683924845 := by
  unfold tailWord_777392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14176907799824513414255215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18902543733099351219006953 14176907799824513414255215)
  ·
    refine ⟨21265361699736770121382823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14176907799824513414255215 21265361699736770121382823)
    ·
      refine ⟨31898042549605155182074235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21265361699736770121382823 31898042549605155182074235)
      ·
        refine ⟨47847063824407732773111353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31898042549605155182074235 47847063824407732773111353)
        ·
          refine ⟨35885297868305799579833515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47847063824407732773111353 35885297868305799579833515)
          ·
            refine ⟨53827946802458699369750273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35885297868305799579833515 53827946802458699369750273)
            ·
              refine ⟨40370960101844024527312705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53827946802458699369750273 40370960101844024527312705)
              ·
                refine ⟨30278220076383018395484529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40370960101844024527312705 30278220076383018395484529)
                ·
                  refine ⟨22708665057287263796613397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30278220076383018395484529 22708665057287263796613397)
                  ·
                    refine ⟨1064468674560340490466253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22708665057287263796613397 1064468674560340490466253)
                    ·
                      refine ⟨399175752960127683924845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1064468674560340490466253 399175752960127683924845)
                      ·
                        rfl

theorem cell23_777392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_777392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777392 prefixEnd_777392 := by exact prefixLift 777392
  have htrace : WordTrace (prefixWord ++ tailWord_777392) baseStart_777392 baseEnd_777392 := by
    simpa [prefixWord, tailWord_777392, baseEnd_777392] using wordTrace_append hprefix tailTrace_777392
  have hstable : (prefixWord ++ tailWord_777392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777392).length < 2 ^ (prefixWord ++ tailWord_777392).sum := by decide
  have hdescent : baseEnd_777392 < baseStart_777392 := by decide
  rcases family_descends (prefixWord ++ tailWord_777392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777393 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 2, 3, 2]
def baseStart_777393 : Nat := 118140960795 + 777393 * 2 ^ 59
def prefixEnd_777393 : Nat := 4983230072969 + 3 ^ 40 * 777393 * 2
def baseEnd_777393 : Nat := 399176266440782180012341

theorem tailTrace_777393 : CollatzResearch.WordTrace tailWord_777393 prefixEnd_777393 399176266440782180012341 := by
  unfold tailWord_777393
  simp only [CollatzResearch.WordTrace]
  refine ⟨28353852072645403999296833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18902568048430269332864555 28353852072645403999296833)
  ·
    refine ⟨21265389054484052999472625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28353852072645403999296833 21265389054484052999472625)
    ·
      refine ⟨15949041790863039749604469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21265389054484052999472625 15949041790863039749604469)
      ·
        refine ⟨1495222667893409976525419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15949041790863039749604469 1495222667893409976525419)
        ·
          refine ⟨2242834001840114964788129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495222667893409976525419 2242834001840114964788129)
          ·
            refine ⟨1682125501380086223591097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2242834001840114964788129 1682125501380086223591097)
            ·
              refine ⟨1261594126035064667693323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1682125501380086223591097 1261594126035064667693323)
              ·
                refine ⟨1892391189052597001539985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261594126035064667693323 1892391189052597001539985)
                ·
                  refine ⟨1419293391789447751154989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892391189052597001539985 1419293391789447751154989)
                  ·
                    refine ⟨532235021921042906683121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419293391789447751154989 532235021921042906683121)
                    ·
                      refine ⟨399176266440782180012341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532235021921042906683121 399176266440782180012341)
                      ·
                        rfl

theorem cell23_777393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_777393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777393 prefixEnd_777393 := by exact prefixLift 777393
  have htrace : WordTrace (prefixWord ++ tailWord_777393) baseStart_777393 baseEnd_777393 := by
    simpa [prefixWord, tailWord_777393, baseEnd_777393] using wordTrace_append hprefix tailTrace_777393
  have hstable : (prefixWord ++ tailWord_777393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777393).length < 2 ^ (prefixWord ++ tailWord_777393).sum := by decide
  have hdescent : baseEnd_777393 < baseStart_777393 := by decide
  rcases family_descends (prefixWord ++ tailWord_777393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777412 : List Nat := [2, 3, 3, 1, 14]
def baseStart_777412 : Nat := 118140960795 + 777412 * 2 ^ 59
def prefixEnd_777412 : Nat := 4983230072969 + 3 ^ 40 * 777412 * 2
def baseEnd_777412 : Nat := 547580277878213450857

theorem tailTrace_777412 : CollatzResearch.WordTrace tailWord_777412 prefixEnd_777412 547580277878213450857 := by
  unfold tailWord_777412
  simp only [CollatzResearch.WordTrace]
  refine ⟨14177272529788285122119245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18903030039717713496158993 14177272529788285122119245)
  ·
    refine ⟨5316477198670606920794717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14177272529788285122119245 5316477198670606920794717)
    ·
      refine ⟨1993678949501477595298019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5316477198670606920794717 1993678949501477595298019)
      ·
        refine ⟨2990518424252216392947029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993678949501477595298019 2990518424252216392947029)
        ·
          refine ⟨547580277878213450857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 2990518424252216392947029 547580277878213450857)
          ·
            rfl

theorem cell23_777412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 14].length) (baseStart_777412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777412 prefixEnd_777412 := by exact prefixLift 777412
  have htrace : WordTrace (prefixWord ++ tailWord_777412) baseStart_777412 baseEnd_777412 := by
    simpa [prefixWord, tailWord_777412, baseEnd_777412] using wordTrace_append hprefix tailTrace_777412
  have hstable : (prefixWord ++ tailWord_777412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777412).length < 2 ^ (prefixWord ++ tailWord_777412).sum := by decide
  have hdescent : baseEnd_777412 < baseStart_777412 := by decide
  rcases family_descends (prefixWord ++ tailWord_777412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777429 : List Nat := [1, 3, 2, 4, 1, 1, 3, 8]
def baseStart_777429 : Nat := 118140960795 + 777429 * 2 ^ 59
def prefixEnd_777429 : Nat := 4983230072969 + 3 ^ 40 * 777429 * 2
def baseEnd_777429 : Nat := 14784990805346075524525

theorem tailTrace_777429 : CollatzResearch.WordTrace tailWord_777429 prefixEnd_777429 14784990805346075524525 := by
  unfold tailWord_777429
  simp only [CollatzResearch.WordTrace]
  refine ⟨28355165100514982147607341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18903443400343321431738227 28355165100514982147607341)
  ·
    refine ⟨10633186912693118305352753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28355165100514982147607341 10633186912693118305352753)
    ·
      refine ⟨7974890184519838729014565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10633186912693118305352753 7974890184519838729014565)
      ·
        refine ⟨1495291909597469761690231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7974890184519838729014565 1495291909597469761690231)
        ·
          refine ⟨2242937864396204642535347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1495291909597469761690231 2242937864396204642535347)
          ·
            refine ⟨3364406796594306963803021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242937864396204642535347 3364406796594306963803021)
            ·
              refine ⟨1261652548722865111426133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3364406796594306963803021 1261652548722865111426133)
              ·
                refine ⟨14784990805346075524525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1261652548722865111426133 14784990805346075524525)
                ·
                  rfl

theorem cell23_777429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 8].length) (baseStart_777429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777429 prefixEnd_777429 := by exact prefixLift 777429
  have htrace : WordTrace (prefixWord ++ tailWord_777429) baseStart_777429 baseEnd_777429 := by
    simpa [prefixWord, tailWord_777429, baseEnd_777429] using wordTrace_append hprefix tailTrace_777429
  have hstable : (prefixWord ++ tailWord_777429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777429).length < 2 ^ (prefixWord ++ tailWord_777429).sum := by decide
  have hdescent : baseEnd_777429 < baseStart_777429 := by decide
  rcases family_descends (prefixWord ++ tailWord_777429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777439 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 3]
def baseStart_777439 : Nat := 118140960795 + 777439 * 2 ^ 59
def prefixEnd_777439 : Nat := 4983230072969 + 3 ^ 40 * 777439 * 2
def baseEnd_777439 : Nat := 399199886550889000037129

theorem tailTrace_777439 : CollatzResearch.WordTrace tailWord_777439 prefixEnd_777439 399199886550889000037129 := by
  unfold tailWord_777439
  simp only [CollatzResearch.WordTrace]
  refine ⟨28355529830478753855471371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18903686553652502570314247 28355529830478753855471371)
  ·
    refine ⟨42533294745718130783207057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28355529830478753855471371 42533294745718130783207057)
    ·
      refine ⟨31899971059288598087405293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42533294745718130783207057 31899971059288598087405293)
      ·
        refine ⟨11962489147233224282776985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31899971059288598087405293 11962489147233224282776985)
        ·
          refine ⟨8971866860424918212082739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11962489147233224282776985 8971866860424918212082739)
          ·
            refine ⟨13457800290637377318124109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8971866860424918212082739 13457800290637377318124109)
            ·
              refine ⟨5046675108989016494296541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13457800290637377318124109 5046675108989016494296541)
              ·
                refine ⟨1892503165870881185361203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5046675108989016494296541 1892503165870881185361203)
                ·
                  refine ⟨2838754748806321778041805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892503165870881185361203 2838754748806321778041805)
                  ·
                    refine ⟨1064533030802370666765677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2838754748806321778041805 1064533030802370666765677)
                    ·
                      refine ⟨399199886550889000037129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1064533030802370666765677 399199886550889000037129)
                      ·
                        rfl

theorem cell23_777439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_777439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777439 prefixEnd_777439 := by exact prefixLift 777439
  have htrace : WordTrace (prefixWord ++ tailWord_777439) baseStart_777439 baseEnd_777439 := by
    simpa [prefixWord, tailWord_777439, baseEnd_777439] using wordTrace_append hprefix tailTrace_777439
  have hstable : (prefixWord ++ tailWord_777439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777439).length < 2 ^ (prefixWord ++ tailWord_777439).sum := by decide
  have hdescent : baseEnd_777439 < baseStart_777439 := by decide
  rcases family_descends (prefixWord ++ tailWord_777439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777473 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_777473 : Nat := 118140960795 + 777473 * 2 ^ 59
def prefixEnd_777473 : Nat := 4983230072969 + 3 ^ 40 * 777473 * 2
def baseEnd_777473 : Nat := 399217344893141867011973

theorem tailTrace_777473 : CollatzResearch.WordTrace tailWord_777473 prefixEnd_777473 399217344893141867011973 := by
  unfold tailWord_777473
  simp only [CollatzResearch.WordTrace]
  refine ⟨28356769912355577662209073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18904513274903718441472715 28356769912355577662209073)
  ·
    refine ⟨21267577434266683246656805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28356769912355577662209073 21267577434266683246656805)
    ·
      refine ⟨3987670768925003108748151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21267577434266683246656805 3987670768925003108748151)
      ·
        refine ⟨5981506153387504663122227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987670768925003108748151 5981506153387504663122227)
        ·
          refine ⟨8972259230081256994683341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5981506153387504663122227 8972259230081256994683341)
          ·
            refine ⟨3364597211280471373006253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8972259230081256994683341 3364597211280471373006253)
            ·
              refine ⟨1261723954230176764877345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3364597211280471373006253 1261723954230176764877345)
              ·
                refine ⟨946292965672632573658009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261723954230176764877345 946292965672632573658009)
                ·
                  refine ⟨709719724254474430243507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 946292965672632573658009 709719724254474430243507)
                  ·
                    refine ⟨1064579586381711645365261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 709719724254474430243507 1064579586381711645365261)
                    ·
                      refine ⟨399217344893141867011973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1064579586381711645365261 399217344893141867011973)
                      ·
                        rfl

theorem cell23_777473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_777473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777473 prefixEnd_777473 := by exact prefixLift 777473
  have htrace : WordTrace (prefixWord ++ tailWord_777473) baseStart_777473 baseEnd_777473 := by
    simpa [prefixWord, tailWord_777473, baseEnd_777473] using wordTrace_append hprefix tailTrace_777473
  have hstable : (prefixWord ++ tailWord_777473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777473).length < 2 ^ (prefixWord ++ tailWord_777473).sum := by decide
  have hdescent : baseEnd_777473 < baseStart_777473 := by decide
  rcases family_descends (prefixWord ++ tailWord_777473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777569 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_777569 : Nat := 118140960795 + 777569 * 2 ^ 59
def prefixEnd_777569 : Nat := 4983230072969 + 3 ^ 40 * 777569 * 2
def baseEnd_777569 : Nat := 399266639035973491411531

theorem tailTrace_777569 : CollatzResearch.WordTrace tailWord_777569 prefixEnd_777569 399266639035973491411531 := by
  unfold tailWord_777569
  simp only [CollatzResearch.WordTrace]
  refine ⟨28360271320007786057703761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18906847546671857371802507 28360271320007786057703761)
  ·
    refine ⟨21270203490005839543277821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28360271320007786057703761 21270203490005839543277821)
    ·
      refine ⟨7976326308752189828729183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21270203490005839543277821 7976326308752189828729183)
      ·
        refine ⟨11964489463128284743093775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7976326308752189828729183 11964489463128284743093775)
        ·
          refine ⟨17946734194692427114640663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11964489463128284743093775 17946734194692427114640663)
          ·
            refine ⟨26920101292038640671960995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17946734194692427114640663 26920101292038640671960995)
            ·
              refine ⟨40380151938057961007941493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26920101292038640671960995 40380151938057961007941493)
              ·
                refine ⟨3785639244192933844494515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40380151938057961007941493 3785639244192933844494515)
                ·
                  refine ⟨5678458866289400766741773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3785639244192933844494515 5678458866289400766741773)
                  ·
                    refine ⟨2129422074858525287528165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5678458866289400766741773 2129422074858525287528165)
                    ·
                      refine ⟨399266639035973491411531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2129422074858525287528165 399266639035973491411531)
                      ·
                        rfl

theorem cell23_777569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_777569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777569 prefixEnd_777569 := by exact prefixLift 777569
  have htrace : WordTrace (prefixWord ++ tailWord_777569) baseStart_777569 baseEnd_777569 := by
    simpa [prefixWord, tailWord_777569, baseEnd_777569] using wordTrace_append hprefix tailTrace_777569
  have hstable : (prefixWord ++ tailWord_777569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777569).length < 2 ^ (prefixWord ++ tailWord_777569).sum := by decide
  have hdescent : baseEnd_777569 < baseStart_777569 := by decide
  rcases family_descends (prefixWord ++ tailWord_777569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777586 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_777586 : Nat := 118140960795 + 777586 * 2 ^ 59
def prefixEnd_777586 : Nat := 4983230072969 + 3 ^ 40 * 777586 * 2
def baseEnd_777586 : Nat := 399275368207099924898953

theorem tailTrace_777586 : CollatzResearch.WordTrace tailWord_777586 prefixEnd_777586 399275368207099924898953 := by
  unfold tailWord_777586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7090222840236549490268153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18907260907297465307381741 7090222840236549490268153)
  ·
    refine ⟨5317667130177412117701115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7090222840236549490268153 5317667130177412117701115)
    ·
      refine ⟨7976500695266118176551673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5317667130177412117701115 7976500695266118176551673)
      ·
        refine ⟨5982375521449588632413755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7976500695266118176551673 5982375521449588632413755)
        ·
          refine ⟨8973563282174382948620633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5982375521449588632413755 8973563282174382948620633)
          ·
            refine ⟨6730172461630787211465475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8973563282174382948620633 6730172461630787211465475)
            ·
              refine ⟨10095258692446180817198213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6730172461630787211465475 10095258692446180817198213)
              ·
                refine ⟨1892861004833658903224665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10095258692446180817198213 1892861004833658903224665)
                ·
                  refine ⟨1419645753625244177418499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892861004833658903224665 1419645753625244177418499)
                  ·
                    refine ⟨2129468630437866266127749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1419645753625244177418499 2129468630437866266127749)
                    ·
                      refine ⟨399275368207099924898953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2129468630437866266127749 399275368207099924898953)
                      ·
                        rfl

theorem cell23_777586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_777586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777586 prefixEnd_777586 := by exact prefixLift 777586
  have htrace : WordTrace (prefixWord ++ tailWord_777586) baseStart_777586 baseEnd_777586 := by
    simpa [prefixWord, tailWord_777586, baseEnd_777586] using wordTrace_append hprefix tailTrace_777586
  have hstable : (prefixWord ++ tailWord_777586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777586).length < 2 ^ (prefixWord ++ tailWord_777586).sum := by decide
  have hdescent : baseEnd_777586 < baseStart_777586 := by decide
  rcases family_descends (prefixWord ++ tailWord_777586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777596 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_777596 : Nat := 118140960795 + 777596 * 2 ^ 59
def prefixEnd_777596 : Nat := 4983230072969 + 3 ^ 40 * 777596 * 2
def baseEnd_777596 : Nat := 133093501004548295257969

theorem tailTrace_777596 : CollatzResearch.WordTrace tailWord_777596 prefixEnd_777596 133093501004548295257969 := by
  unfold tailWord_777596
  simp only [CollatzResearch.WordTrace]
  refine ⟨14180628045454984834468321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18907504060606646445957761 14180628045454984834468321)
  ·
    refine ⟨10635471034091238625851241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14180628045454984834468321 10635471034091238625851241)
    ·
      refine ⟨7976603275568428969388431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10635471034091238625851241 7976603275568428969388431)
      ·
        refine ⟨11964904913352643454082647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7976603275568428969388431 11964904913352643454082647)
        ·
          refine ⟨17947357370028965181123971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11964904913352643454082647 17947357370028965181123971)
          ·
            refine ⟨26921036055043447771685957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17947357370028965181123971 26921036055043447771685957)
            ·
              refine ⟨5047694260320646457191117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26921036055043447771685957 5047694260320646457191117)
              ·
                refine ⟨1892885347620242421446669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5047694260320646457191117 1892885347620242421446669)
                ·
                  refine ⟨709832005357590908042501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1892885347620242421446669 709832005357590908042501)
                  ·
                    refine ⟨133093501004548295257969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 709832005357590908042501 133093501004548295257969)
                    ·
                      rfl

theorem cell23_777596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_777596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777596 prefixEnd_777596 := by exact prefixLift 777596
  have htrace : WordTrace (prefixWord ++ tailWord_777596) baseStart_777596 baseEnd_777596 := by
    simpa [prefixWord, tailWord_777596, baseEnd_777596] using wordTrace_append hprefix tailTrace_777596
  have hstable : (prefixWord ++ tailWord_777596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777596).length < 2 ^ (prefixWord ++ tailWord_777596).sum := by decide
  have hdescent : baseEnd_777596 < baseStart_777596 := by decide
  rcases family_descends (prefixWord ++ tailWord_777596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777603 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 2, 4, 2]
def baseStart_777603 : Nat := 118140960795 + 777603 * 2 ^ 59
def prefixEnd_777603 : Nat := 4983230072969 + 3 ^ 40 * 777603 * 2
def baseEnd_777603 : Nat := 399284097378226358386375

theorem tailTrace_777603 : CollatzResearch.WordTrace tailWord_777603 prefixEnd_777603 399284097378226358386375 := by
  unfold tailWord_777603
  simp only [CollatzResearch.WordTrace]
  refine ⟨28361511401884609864441463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18907674267923073242960975 28361511401884609864441463)
  ·
    refine ⟨42542267102826914796662195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28361511401884609864441463 42542267102826914796662195)
    ·
      refine ⟨63813400654240372194993293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42542267102826914796662195 63813400654240372194993293)
      ·
        refine ⟨23930025245340139573122485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63813400654240372194993293 23930025245340139573122485)
        ·
          refine ⟨2243439866750638084980233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23930025245340139573122485 2243439866750638084980233)
          ·
            refine ⟨1682579900062978563735175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2243439866750638084980233 1682579900062978563735175)
            ·
              refine ⟨2523869850094467845602763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682579900062978563735175 2523869850094467845602763)
              ·
                refine ⟨3785804775141701768404145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2523869850094467845602763 3785804775141701768404145)
                ·
                  refine ⟨2839353581356276326303109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3785804775141701768404145 2839353581356276326303109)
                  ·
                    refine ⟨532378796504301811181833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2839353581356276326303109 532378796504301811181833)
                    ·
                      refine ⟨399284097378226358386375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532378796504301811181833 399284097378226358386375)
                      ·
                        rfl

theorem cell23_777603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_777603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777603 prefixEnd_777603 := by exact prefixLift 777603
  have htrace : WordTrace (prefixWord ++ tailWord_777603) baseStart_777603 baseEnd_777603 := by
    simpa [prefixWord, tailWord_777603, baseEnd_777603] using wordTrace_append hprefix tailTrace_777603
  have hstable : (prefixWord ++ tailWord_777603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777603).length < 2 ^ (prefixWord ++ tailWord_777603).sum := by decide
  have hdescent : baseEnd_777603 < baseStart_777603 := by decide
  rcases family_descends (prefixWord ++ tailWord_777603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777620 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 2, 1, 4]
def baseStart_777620 : Nat := 118140960795 + 777620 * 2 ^ 59
def prefixEnd_777620 : Nat := 4983230072969 + 3 ^ 40 * 777620 * 2
def baseEnd_777620 : Nat := 399292826549352791873797

theorem tailTrace_777620 : CollatzResearch.WordTrace tailWord_777620 prefixEnd_777620 399292826549352791873797 := by
  unfold tailWord_777620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14181065721411510883905157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18908087628548681178540209 14181065721411510883905157)
  ·
    refine ⟨2658949822764658290732217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14181065721411510883905157 2658949822764658290732217)
    ·
      refine ⟨1994212367073493718049163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2658949822764658290732217 1994212367073493718049163)
      ·
        refine ⟨2991318550610240577073745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994212367073493718049163 2991318550610240577073745)
        ·
          refine ⟨2243488912957680432805309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2991318550610240577073745 2243488912957680432805309)
          ·
            refine ⟨841308342359130162301991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2243488912957680432805309 841308342359130162301991)
            ·
              refine ⟨1261962513538695243452987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841308342359130162301991 1261962513538695243452987)
              ·
                refine ⟨1892943770308042865179481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261962513538695243452987 1892943770308042865179481)
                ·
                  refine ⟨1419707827731032148884611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1892943770308042865179481 1419707827731032148884611)
                  ·
                    refine ⟨2129561741596548223326917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1419707827731032148884611 2129561741596548223326917)
                    ·
                      refine ⟨399292826549352791873797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2129561741596548223326917 399292826549352791873797)
                      ·
                        rfl

theorem cell23_777620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_777620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777620 prefixEnd_777620 := by exact prefixLift 777620
  have htrace : WordTrace (prefixWord ++ tailWord_777620) baseStart_777620 baseEnd_777620 := by
    simpa [prefixWord, tailWord_777620, baseEnd_777620] using wordTrace_append hprefix tailTrace_777620
  have hstable : (prefixWord ++ tailWord_777620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777620).length < 2 ^ (prefixWord ++ tailWord_777620).sum := by decide
  have hdescent : baseEnd_777620 < baseStart_777620 := by decide
  rcases family_descends (prefixWord ++ tailWord_777620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777660 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 6]
def baseStart_777660 : Nat := 118140960795 + 777660 * 2 ^ 59
def prefixEnd_777660 : Nat := 4983230072969 + 3 ^ 40 * 777660 * 2
def baseEnd_777660 : Nat := 44368151752836959485957

theorem tailTrace_777660 : CollatzResearch.WordTrace tailWord_777660 prefixEnd_777660 44368151752836959485957 := by
  unfold tailWord_777660
  simp only [CollatzResearch.WordTrace]
  refine ⟨14181795181339054299633217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18909060241785405732844289 14181795181339054299633217)
  ·
    refine ⟨10636346386004290724724913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14181795181339054299633217 10636346386004290724724913)
    ·
      refine ⟨7977259789503218043543685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10636346386004290724724913 7977259789503218043543685)
      ·
        refine ⟨1495736210531853383164441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7977259789503218043543685 1495736210531853383164441)
        ·
          refine ⟨1121802157898890037373331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1495736210531853383164441 1121802157898890037373331)
          ·
            refine ⟨1682703236848335056059997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121802157898890037373331 1682703236848335056059997)
            ·
              refine ⟨631013713818125646022499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1682703236848335056059997 631013713818125646022499)
              ·
                refine ⟨946520570727188469033749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631013713818125646022499 946520570727188469033749)
                ·
                  refine ⟨44368151752836959485957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 946520570727188469033749 44368151752836959485957)
                  ·
                    rfl

theorem cell23_777660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_777660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777660 prefixEnd_777660 := by exact prefixLift 777660
  have htrace : WordTrace (prefixWord ++ tailWord_777660) baseStart_777660 baseEnd_777660 := by
    simpa [prefixWord, tailWord_777660, baseEnd_777660] using wordTrace_append hprefix tailTrace_777660
  have hstable : (prefixWord ++ tailWord_777660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777660).length < 2 ^ (prefixWord ++ tailWord_777660).sum := by decide
  have hdescent : baseEnd_777660 < baseStart_777660 := by decide
  rcases family_descends (prefixWord ++ tailWord_777660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777703 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 4, 4]
def baseStart_777703 : Nat := 118140960795 + 777703 * 2 ^ 59
def prefixEnd_777703 : Nat := 4983230072969 + 3 ^ 40 * 777703 * 2
def baseEnd_777703 : Nat := 133111815147891989045305

theorem tailTrace_777703 : CollatzResearch.WordTrace tailWord_777703 prefixEnd_777703 133111815147891989045305 := by
  unfold tailWord_777703
  simp only [CollatzResearch.WordTrace]
  refine ⟨28365158701522326943081763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18910105801014884628721175 28365158701522326943081763)
  ·
    refine ⟨42547738052283490414622645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28365158701522326943081763 42547738052283490414622645)
    ·
      refine ⟨3988850442401577226370873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42547738052283490414622645 3988850442401577226370873)
      ·
        refine ⟨2991637831801182919778155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3988850442401577226370873 2991637831801182919778155)
        ·
          refine ⟨4487456747701774379667233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991637831801182919778155 4487456747701774379667233)
          ·
            refine ⟨3365592560776330784750425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4487456747701774379667233 3365592560776330784750425)
            ·
              refine ⟨2524194420582248088562819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3365592560776330784750425 2524194420582248088562819)
              ·
                refine ⟨3786291630873372132844229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2524194420582248088562819 3786291630873372132844229)
                ·
                  refine ⟨709929680788757274908293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3786291630873372132844229 709929680788757274908293)
                  ·
                    refine ⟨133111815147891989045305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 709929680788757274908293 133111815147891989045305)
                    ·
                      rfl

theorem cell23_777703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_777703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777703 prefixEnd_777703 := by exact prefixLift 777703
  have htrace : WordTrace (prefixWord ++ tailWord_777703) baseStart_777703 baseEnd_777703 := by
    simpa [prefixWord, tailWord_777703, baseEnd_777703] using wordTrace_append hprefix tailTrace_777703
  have hstable : (prefixWord ++ tailWord_777703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777703).length < 2 ^ (prefixWord ++ tailWord_777703).sum := by decide
  have hdescent : baseEnd_777703 < baseStart_777703 := by decide
  rcases family_descends (prefixWord ++ tailWord_777703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777720 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 2, 4]
def baseStart_777720 : Nat := 118140960795 + 777720 * 2 ^ 59
def prefixEnd_777720 : Nat := 4983230072969 + 3 ^ 40 * 777720 * 2
def baseEnd_777720 : Nat := 133114724871600800207779

theorem tailTrace_777720 : CollatzResearch.WordTrace tailWord_777720 prefixEnd_777720 133114724871600800207779 := by
  unfold tailWord_777720
  simp only [CollatzResearch.WordTrace]
  refine ⟨14182889371230369423225307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18910519161640492564300409 14182889371230369423225307)
  ·
    refine ⟨21274334056845554134837961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14182889371230369423225307 21274334056845554134837961)
    ·
      refine ⟨15955750542634165601128471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21274334056845554134837961 15955750542634165601128471)
      ·
        refine ⟨23933625813951248401692707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15955750542634165601128471 23933625813951248401692707)
        ·
          refine ⟨35900438720926872602539061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23933625813951248401692707 35900438720926872602539061)
          ·
            refine ⟨3365666130086894306488037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35900438720926872602539061 3365666130086894306488037)
            ·
              refine ⟨631062399391292682466507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3365666130086894306488037 631062399391292682466507)
              ·
                refine ⟨946593599086939023699761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631062399391292682466507 946593599086939023699761)
                ·
                  refine ⟨709945199315204267774821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 946593599086939023699761 709945199315204267774821)
                  ·
                    refine ⟨133114724871600800207779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 709945199315204267774821 133114724871600800207779)
                    ·
                      rfl

theorem cell23_777720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_777720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777720 prefixEnd_777720 := by exact prefixLift 777720
  have htrace : WordTrace (prefixWord ++ tailWord_777720) baseStart_777720 baseEnd_777720 := by
    simpa [prefixWord, tailWord_777720, baseEnd_777720] using wordTrace_append hprefix tailTrace_777720
  have hstable : (prefixWord ++ tailWord_777720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777720).length < 2 ^ (prefixWord ++ tailWord_777720).sum := by decide
  have hdescent : baseEnd_777720 < baseStart_777720 := by decide
  rcases family_descends (prefixWord ++ tailWord_777720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777753 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 7, 3, 2]
def baseStart_777753 : Nat := 118140960795 + 777753 * 2 ^ 59
def prefixEnd_777753 : Nat := 4983230072969 + 3 ^ 40 * 777753 * 2
def baseEnd_777753 : Nat := 399361119476400771510685

theorem tailTrace_777753 : CollatzResearch.WordTrace tailWord_777753 prefixEnd_777753 399361119476400771510685 := by
  unfold tailWord_777753
  simp only [CollatzResearch.WordTrace]
  refine ⟨28366982351341185482401913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18911321567560790321601275 28366982351341185482401913)
  ·
    refine ⟨21275236763505889111801435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28366982351341185482401913 21275236763505889111801435)
    ·
      refine ⟨31912855145258833667702153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21275236763505889111801435 31912855145258833667702153)
      ·
        refine ⟨23934641358944125250776615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31912855145258833667702153 23934641358944125250776615)
        ·
          refine ⟨35901962038416187876164923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23934641358944125250776615 35901962038416187876164923)
          ·
            refine ⟨53852943057624281814247385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35901962038416187876164923 53852943057624281814247385)
            ·
              refine ⟨40389707293218211360685539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53852943057624281814247385 40389707293218211360685539)
              ·
                refine ⟨60584560939827317041028309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40389707293218211360685539 60584560939827317041028309)
                ·
                  refine ⟨1419950647027202743149101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60584560939827317041028309 1419950647027202743149101)
                  ·
                    refine ⟨532481492635201028680913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419950647027202743149101 532481492635201028680913)
                    ·
                      refine ⟨399361119476400771510685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532481492635201028680913 399361119476400771510685)
                      ·
                        rfl

theorem cell23_777753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_777753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777753 prefixEnd_777753 := by exact prefixLift 777753
  have htrace : WordTrace (prefixWord ++ tailWord_777753) baseStart_777753 baseEnd_777753 := by
    simpa [prefixWord, tailWord_777753, baseEnd_777753] using wordTrace_append hprefix tailTrace_777753
  have hstable : (prefixWord ++ tailWord_777753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777753).length < 2 ^ (prefixWord ++ tailWord_777753).sum := by decide
  have hdescent : baseEnd_777753 < baseStart_777753 := by decide
  rcases family_descends (prefixWord ++ tailWord_777753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777761 : List Nat := [1, 2, 3, 2, 2, 4, 2, 2, 1, 2, 2]
def baseStart_777761 : Nat := 118140960795 + 777761 * 2 ^ 59
def prefixEnd_777761 : Nat := 4983230072969 + 3 ^ 40 * 777761 * 2
def baseEnd_777761 : Nat := 399365227321636740210649

theorem tailTrace_777761 : CollatzResearch.WordTrace tailWord_777761 prefixEnd_777761 399365227321636740210649 := by
  unfold tailWord_777761
  simp only [CollatzResearch.WordTrace]
  refine ⟨28367274135312202848693137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18911516090208135232462091 28367274135312202848693137)
  ·
    refine ⟨21275455601484152136519853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28367274135312202848693137 21275455601484152136519853)
    ·
      refine ⟨7978295850556557051194945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21275455601484152136519853 7978295850556557051194945)
      ·
        refine ⟨5983721887917417788396209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7978295850556557051194945 5983721887917417788396209)
        ·
          refine ⟨4487791415938063341297157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5983721887917417788396209 4487791415938063341297157)
          ·
            refine ⟨841460890488386876493217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4487791415938063341297157 841460890488386876493217)
            ·
              refine ⟨631095667866290157369913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841460890488386876493217 631095667866290157369913)
              ·
                refine ⟨473321750899717618027435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631095667866290157369913 473321750899717618027435)
                ·
                  refine ⟨709982626349576427041153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473321750899717618027435 709982626349576427041153)
                  ·
                    refine ⟨532486969762182320280865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 709982626349576427041153 532486969762182320280865)
                    ·
                      refine ⟨399365227321636740210649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532486969762182320280865 399365227321636740210649)
                      ·
                        rfl

theorem cell23_777761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_777761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777761 prefixEnd_777761 := by exact prefixLift 777761
  have htrace : WordTrace (prefixWord ++ tailWord_777761) baseStart_777761 baseEnd_777761 := by
    simpa [prefixWord, tailWord_777761, baseEnd_777761] using wordTrace_append hprefix tailTrace_777761
  have hstable : (prefixWord ++ tailWord_777761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777761).length < 2 ^ (prefixWord ++ tailWord_777761).sum := by decide
  have hdescent : baseEnd_777761 < baseStart_777761 := by decide
  rcases family_descends (prefixWord ++ tailWord_777761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777770 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_777770 : Nat := 118140960795 + 777770 * 2 ^ 59
def prefixEnd_777770 : Nat := 4983230072969 + 3 ^ 40 * 777770 * 2
def baseEnd_777770 : Nat := 399369848647527204998107

theorem tailTrace_777770 : CollatzResearch.WordTrace tailWord_777770 prefixEnd_777770 399369848647527204998107 := by
  unfold tailWord_777770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7091900598069899346442691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18911734928186398257180509 7091900598069899346442691)
  ·
    refine ⟨10637850897104849019664037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7091900598069899346442691 10637850897104849019664037)
    ·
      refine ⟨1994597043207159191187007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10637850897104849019664037 1994597043207159191187007)
      ·
        refine ⟨2991895564810738786780511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994597043207159191187007 2991895564810738786780511)
        ·
          refine ⟨4487843347216108180170767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991895564810738786780511 4487843347216108180170767)
          ·
            refine ⟨6731765020824162270256151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487843347216108180170767 6731765020824162270256151)
            ·
              refine ⟨10097647531236243405384227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6731765020824162270256151 10097647531236243405384227)
              ·
                refine ⟨15146471296854365108076341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10097647531236243405384227 15146471296854365108076341)
                ·
                  refine ⟨1419981684080096728882157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15146471296854365108076341 1419981684080096728882157)
                  ·
                    refine ⟨532493131530036273330809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1419981684080096728882157 532493131530036273330809)
                    ·
                      refine ⟨399369848647527204998107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532493131530036273330809 399369848647527204998107)
                      ·
                        rfl

theorem cell23_777770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_777770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777770 prefixEnd_777770 := by exact prefixLift 777770
  have htrace : WordTrace (prefixWord ++ tailWord_777770) baseStart_777770 baseEnd_777770 := by
    simpa [prefixWord, tailWord_777770, baseEnd_777770] using wordTrace_append hprefix tailTrace_777770
  have hstable : (prefixWord ++ tailWord_777770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777770).length < 2 ^ (prefixWord ++ tailWord_777770).sum := by decide
  have hdescent : baseEnd_777770 < baseStart_777770 := by decide
  rcases family_descends (prefixWord ++ tailWord_777770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777798 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_777798 : Nat := 118140960795 + 777798 * 2 ^ 59
def prefixEnd_777798 : Nat := 4983230072969 + 3 ^ 40 * 777798 * 2
def baseEnd_777798 : Nat := 399384226105853095447979

theorem tailTrace_777798 : CollatzResearch.WordTrace tailWord_777798 prefixEnd_777798 399384226105853095447979 := by
  unfold tailWord_777798
  simp only [CollatzResearch.WordTrace]
  refine ⟨886519488630567442743439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18912415757452105445193365 886519488630567442743439)
  ·
    refine ⟨1329779232945851164115159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 886519488630567442743439 1329779232945851164115159)
    ·
      refine ⟨1994668849418776746172739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1329779232945851164115159 1994668849418776746172739)
      ·
        refine ⟨2992003274128165119259109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994668849418776746172739 2992003274128165119259109)
        ·
          refine ⟨561000613899030959861083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2992003274128165119259109 561000613899030959861083)
          ·
            refine ⟨841500920848546439791625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561000613899030959861083 841500920848546439791625)
            ·
              refine ⟨631125690636409829843719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841500920848546439791625 631125690636409829843719)
              ·
                refine ⟨946688535954614744765579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631125690636409829843719 946688535954614744765579)
                ·
                  refine ⟨1420032803931922117148369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946688535954614744765579 1420032803931922117148369)
                  ·
                    refine ⟨1065024602948941587861277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1420032803931922117148369 1065024602948941587861277)
                    ·
                      refine ⟨399384226105853095447979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1065024602948941587861277 399384226105853095447979)
                      ·
                        rfl

theorem cell23_777798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_777798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777798 prefixEnd_777798 := by exact prefixLift 777798
  have htrace : WordTrace (prefixWord ++ tailWord_777798) baseStart_777798 baseEnd_777798 := by
    simpa [prefixWord, tailWord_777798, baseEnd_777798] using wordTrace_append hprefix tailTrace_777798
  have hstable : (prefixWord ++ tailWord_777798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777798).length < 2 ^ (prefixWord ++ tailWord_777798).sum := by decide
  have hdescent : baseEnd_777798 < baseStart_777798 := by decide
  rcases family_descends (prefixWord ++ tailWord_777798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777804 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 1, 3, 2]
def baseStart_777804 : Nat := 118140960795 + 777804 * 2 ^ 59
def prefixEnd_777804 : Nat := 4983230072969 + 3 ^ 40 * 777804 * 2
def baseEnd_777804 : Nat := 399387306989780071972951

theorem tailTrace_777804 : CollatzResearch.WordTrace tailWord_777804 prefixEnd_777804 399387306989780071972951 := by
  unfold tailWord_777804
  simp only [CollatzResearch.WordTrace]
  refine ⟨14184421237078210596254233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18912561649437614128338977 14184421237078210596254233)
  ·
    refine ⟨10638315927808657947190675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14184421237078210596254233 10638315927808657947190675)
    ·
      refine ⟨15957473891712986920786013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10638315927808657947190675 15957473891712986920786013)
      ·
        refine ⟨5984052709392370095294755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15957473891712986920786013 5984052709392370095294755)
        ·
          refine ⟨8976079064088555142942133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5984052709392370095294755 8976079064088555142942133)
          ·
            refine ⟨841507412258302044650825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8976079064088555142942133 841507412258302044650825)
            ·
              refine ⟨631130559193726533488119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841507412258302044650825 631130559193726533488119)
              ·
                refine ⟨946695838790589800232179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631130559193726533488119 946695838790589800232179)
                ·
                  refine ⟨1420043758185884700348269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946695838790589800232179 1420043758185884700348269)
                  ·
                    refine ⟨532516409319706762630601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1420043758185884700348269 532516409319706762630601)
                    ·
                      refine ⟨399387306989780071972951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532516409319706762630601 399387306989780071972951)
                      ·
                        rfl

theorem cell23_777804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_777804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777804 prefixEnd_777804 := by exact prefixLift 777804
  have htrace : WordTrace (prefixWord ++ tailWord_777804) baseStart_777804 baseEnd_777804 := by
    simpa [prefixWord, tailWord_777804, baseEnd_777804] using wordTrace_append hprefix tailTrace_777804
  have hstable : (prefixWord ++ tailWord_777804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777804).length < 2 ^ (prefixWord ++ tailWord_777804).sum := by decide
  have hdescent : baseEnd_777804 < baseStart_777804 := by decide
  rcases family_descends (prefixWord ++ tailWord_777804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777806 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_777806 : Nat := 118140960795 + 777806 * 2 ^ 59
def prefixEnd_777806 : Nat := 4983230072969 + 3 ^ 40 * 777806 * 2
def baseEnd_777806 : Nat := 44376481550121007127549

theorem tailTrace_777806 : CollatzResearch.WordTrace tailWord_777806 prefixEnd_777806 44376481550121007127549 := by
  unfold tailWord_777806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546114427518646941760159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18912610280099450356054181 3546114427518646941760159)
  ·
    refine ⟨5319171641277970412640239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3546114427518646941760159 5319171641277970412640239)
    ·
      refine ⟨7978757461916955618960359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319171641277970412640239 7978757461916955618960359)
      ·
        refine ⟨11968136192875433428440539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7978757461916955618960359 11968136192875433428440539)
        ·
          refine ⟨17952204289313150142660809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11968136192875433428440539 17952204289313150142660809)
          ·
            refine ⟨13464153216984862606995607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17952204289313150142660809 13464153216984862606995607)
            ·
              refine ⟨20196229825477293910493411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13464153216984862606995607 20196229825477293910493411)
              ·
                refine ⟨30294344738215940865740117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20196229825477293910493411 30294344738215940865740117)
                ·
                  refine ⟨44376481550121007127549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 30294344738215940865740117 44376481550121007127549)
                  ·
                    rfl

theorem cell23_777806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_777806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777806 prefixEnd_777806 := by exact prefixLift 777806
  have htrace : WordTrace (prefixWord ++ tailWord_777806) baseStart_777806 baseEnd_777806 := by
    simpa [prefixWord, tailWord_777806, baseEnd_777806] using wordTrace_append hprefix tailTrace_777806
  have hstable : (prefixWord ++ tailWord_777806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777806).length < 2 ^ (prefixWord ++ tailWord_777806).sum := by decide
  have hdescent : baseEnd_777806 < baseStart_777806 := by decide
  rcases family_descends (prefixWord ++ tailWord_777806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777833 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 3]
def baseStart_777833 : Nat := 118140960795 + 777833 * 2 ^ 59
def prefixEnd_777833 : Nat := 4983230072969 + 3 ^ 40 * 777833 * 2
def baseEnd_777833 : Nat := 399402197928760458510317

theorem tailTrace_777833 : CollatzResearch.WordTrace tailWord_777833 prefixEnd_777833 399402197928760458510317 := by
  unfold tailWord_777833
  simp only [CollatzResearch.WordTrace]
  refine ⟨28369900191051359145314153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18913266794034239430209435 28369900191051359145314153)
  ·
    refine ⟨21277425143288519358985615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28369900191051359145314153 21277425143288519358985615)
    ·
      refine ⟨31916137714932779038478423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21277425143288519358985615 31916137714932779038478423)
      ·
        refine ⟨47874206572399168557717635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31916137714932779038478423 47874206572399168557717635)
        ·
          refine ⟨71811309858598752836576453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47874206572399168557717635 71811309858598752836576453)
          ·
            refine ⟨13464620598487266156858085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71811309858598752836576453 13464620598487266156858085)
            ·
              refine ⟨2524616362216362404410891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13464620598487266156858085 2524616362216362404410891)
              ·
                refine ⟨3786924543324543606616337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2524616362216362404410891 3786924543324543606616337)
                ·
                  refine ⟨2840193407493407704962253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3786924543324543606616337 2840193407493407704962253)
                  ·
                    refine ⟨1065072527810027889360845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2840193407493407704962253 1065072527810027889360845)
                    ·
                      refine ⟨399402197928760458510317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1065072527810027889360845 399402197928760458510317)
                      ·
                        rfl

theorem cell23_777833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_777833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777833 prefixEnd_777833 := by exact prefixLift 777833
  have htrace : WordTrace (prefixWord ++ tailWord_777833) baseStart_777833 baseEnd_777833 := by
    simpa [prefixWord, tailWord_777833, baseEnd_777833] using wordTrace_append hprefix tailTrace_777833
  have hstable : (prefixWord ++ tailWord_777833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777833).length < 2 ^ (prefixWord ++ tailWord_777833).sum := by decide
  have hdescent : baseEnd_777833 < baseStart_777833 := by decide
  rcases family_descends (prefixWord ++ tailWord_777833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777843 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 3, 7, 2]
def baseStart_777843 : Nat := 118140960795 + 777843 * 2 ^ 59
def prefixEnd_777843 : Nat := 4983230072969 + 3 ^ 40 * 777843 * 2
def baseEnd_777843 : Nat := 399407332735305419385271

theorem tailTrace_777843 : CollatzResearch.WordTrace tailWord_777843 prefixEnd_777843 399407332735305419385271 := by
  unfold tailWord_777843
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370264921015130853178183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18913509947343420568785455 28370264921015130853178183)
  ·
    refine ⟨42555397381522696279767275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28370264921015130853178183 42555397381522696279767275)
    ·
      refine ⟨63833096072284044419650913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42555397381522696279767275 63833096072284044419650913)
      ·
        refine ⟨47874822054213033314738185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63833096072284044419650913 47874822054213033314738185)
        ·
          refine ⟨35906116540659774986053639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47874822054213033314738185 35906116540659774986053639)
          ·
            refine ⟨53859174810989662479080459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35906116540659774986053639 53859174810989662479080459)
            ·
              refine ⟨80788762216484493718620689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53859174810989662479080459 80788762216484493718620689)
              ·
                refine ⟨60591571662363370288965517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80788762216484493718620689 60591571662363370288965517)
                ·
                  refine ⟨22721839373386263858362069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60591571662363370288965517 22721839373386263858362069)
                  ·
                    refine ⟨532543110313740559180361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22721839373386263858362069 532543110313740559180361)
                    ·
                      refine ⟨399407332735305419385271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532543110313740559180361 399407332735305419385271)
                      ·
                        rfl

theorem cell23_777843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 7, 2].length) (baseStart_777843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777843 prefixEnd_777843 := by exact prefixLift 777843
  have htrace : WordTrace (prefixWord ++ tailWord_777843) baseStart_777843 baseEnd_777843 := by
    simpa [prefixWord, tailWord_777843, baseEnd_777843] using wordTrace_append hprefix tailTrace_777843
  have hstable : (prefixWord ++ tailWord_777843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777843).length < 2 ^ (prefixWord ++ tailWord_777843).sum := by decide
  have hdescent : baseEnd_777843 < baseStart_777843 := by decide
  rcases family_descends (prefixWord ++ tailWord_777843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777853 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_777853 : Nat := 118140960795 + 777853 * 2 ^ 59
def prefixEnd_777853 : Nat := 4983230072969 + 3 ^ 40 * 777853 * 2
def baseEnd_777853 : Nat := 133137489180616793420075

theorem tailTrace_777853 : CollatzResearch.WordTrace tailWord_777853 prefixEnd_777853 133137489180616793420075 := by
  unfold tailWord_777853
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370629650978902561042213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18913753100652601707361475 28370629650978902561042213)
  ·
    refine ⟨5319493059558544230195415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28370629650978902561042213 5319493059558544230195415)
    ·
      refine ⟨7979239589337816345293123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319493059558544230195415 7979239589337816345293123)
      ·
        refine ⟨11968859384006724517939685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7979239589337816345293123 11968859384006724517939685)
        ·
          refine ⟨2244161134501260847113691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11968859384006724517939685 2244161134501260847113691)
          ·
            refine ⟨3366241701751891270670537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244161134501260847113691 3366241701751891270670537)
            ·
              refine ⟨2524681276313918453002903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366241701751891270670537 2524681276313918453002903)
              ·
                refine ⟨3787021914470877679504355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2524681276313918453002903 3787021914470877679504355)
                ·
                  refine ⟨5680532871706316519256533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787021914470877679504355 5680532871706316519256533)
                  ·
                    refine ⟨133137489180616793420075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5680532871706316519256533 133137489180616793420075)
                    ·
                      rfl

theorem cell23_777853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_777853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777853 prefixEnd_777853 := by exact prefixLift 777853
  have htrace : WordTrace (prefixWord ++ tailWord_777853) baseStart_777853 baseEnd_777853 := by
    simpa [prefixWord, tailWord_777853, baseEnd_777853] using wordTrace_append hprefix tailTrace_777853
  have hstable : (prefixWord ++ tailWord_777853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777853).length < 2 ^ (prefixWord ++ tailWord_777853).sum := by decide
  have hdescent : baseEnd_777853 < baseStart_777853 := by decide
  rcases family_descends (prefixWord ++ tailWord_777853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777857 : List Nat := [1, 2, 4, 2, 1, 4, 1, 3, 5]
def baseStart_777857 : Nat := 118140960795 + 777857 * 2 ^ 59
def prefixEnd_777857 : Nat := 4983230072969 + 3 ^ 40 * 777857 * 2
def baseEnd_777857 : Nat := 44379391273829818290023

theorem tailTrace_777857 : CollatzResearch.WordTrace tailWord_777857 prefixEnd_777857 44379391273829818290023 := by
  unfold tailWord_777857
  simp only [CollatzResearch.WordTrace]
  refine ⟨28370775542964411244187825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18913850361976274162791883 28370775542964411244187825)
  ·
    refine ⟨21278081657223308433140869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28370775542964411244187825 21278081657223308433140869)
    ·
      refine ⟨3989640310729370331213913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21278081657223308433140869 3989640310729370331213913)
      ·
        refine ⟨2992230233047027748410435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3989640310729370331213913 2992230233047027748410435)
        ·
          refine ⟨4488345349570541622615653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992230233047027748410435 4488345349570541622615653)
          ·
            refine ⟨841564753044476554240435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4488345349570541622615653 841564753044476554240435)
            ·
              refine ⟨1262347129566714831360653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841564753044476554240435 1262347129566714831360653)
              ·
                refine ⟨473380173587518061760245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1262347129566714831360653 473380173587518061760245)
                ·
                  refine ⟨44379391273829818290023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 473380173587518061760245 44379391273829818290023)
                  ·
                    rfl

theorem cell23_777857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 5].length) (baseStart_777857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777857 prefixEnd_777857 := by exact prefixLift 777857
  have htrace : WordTrace (prefixWord ++ tailWord_777857) baseStart_777857 baseEnd_777857 := by
    simpa [prefixWord, tailWord_777857, baseEnd_777857] using wordTrace_append hprefix tailTrace_777857
  have hstable : (prefixWord ++ tailWord_777857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777857).length < 2 ^ (prefixWord ++ tailWord_777857).sum := by decide
  have hdescent : baseEnd_777857 < baseStart_777857 := by decide
  rcases family_descends (prefixWord ++ tailWord_777857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777870 : List Nat := [4, 1, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_777870 : Nat := 118140960795 + 777870 * 2 ^ 59
def prefixEnd_777870 : Nat := 4983230072969 + 3 ^ 40 * 777870 * 2
def baseEnd_777870 : Nat := 133140398904325604582549

theorem tailTrace_777870 : CollatzResearch.WordTrace tailWord_777870 prefixEnd_777870 133140398904325604582549 := by
  unfold tailWord_777870
  simp only [CollatzResearch.WordTrace]
  refine ⟨3546406211489664308051383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18914166461278209642940709 3546406211489664308051383)
  ·
    refine ⟨5319609317234496462077075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3546406211489664308051383 5319609317234496462077075)
    ·
      refine ⟨7979413975851744693115613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319609317234496462077075 7979413975851744693115613)
      ·
        refine ⟨2992280240944404259918355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7979413975851744693115613 2992280240944404259918355)
        ·
          refine ⟨4488420361416606389877533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992280240944404259918355 4488420361416606389877533)
          ·
            refine ⟨1683157635531227396204075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4488420361416606389877533 1683157635531227396204075)
            ·
              refine ⟨2524736453296841094306113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683157635531227396204075 2524736453296841094306113)
              ·
                refine ⟨1893552339972630820729585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2524736453296841094306113 1893552339972630820729585)
                ·
                  refine ⟨1420164254979473115547189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1893552339972630820729585 1420164254979473115547189)
                  ·
                    refine ⟨133140398904325604582549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1420164254979473115547189 133140398904325604582549)
                    ·
                      rfl

theorem cell23_777870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_777870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777870 prefixEnd_777870 := by exact prefixLift 777870
  have htrace : WordTrace (prefixWord ++ tailWord_777870) baseStart_777870 baseEnd_777870 := by
    simpa [prefixWord, tailWord_777870, baseEnd_777870] using wordTrace_append hprefix tailTrace_777870
  have hstable : (prefixWord ++ tailWord_777870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777870).length < 2 ^ (prefixWord ++ tailWord_777870).sum := by decide
  have hdescent : baseEnd_777870 < baseStart_777870 := by decide
  rcases family_descends (prefixWord ++ tailWord_777870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777874 : List Nat := [3, 2, 3, 1, 3, 1, 3, 2, 5]
def baseStart_777874 : Nat := 118140960795 + 777874 * 2 ^ 59
def prefixEnd_777874 : Nat := 4983230072969 + 3 ^ 40 * 777874 * 2
def baseEnd_777874 : Nat := 44380361181732755344181

theorem tailTrace_777874 : CollatzResearch.WordTrace tailWord_777874 prefixEnd_777874 44380361181732755344181 := by
  unfold tailWord_777874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7092848895975705786889169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18914263722601882098371117 7092848895975705786889169)
  ·
    refine ⟨5319636671981779340166877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7092848895975705786889169 5319636671981779340166877)
    ·
      refine ⟨1994863751993167252562579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5319636671981779340166877 1994863751993167252562579)
      ·
        refine ⟨2992295627989750878843869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994863751993167252562579 2992295627989750878843869)
        ·
          refine ⟨1122110860496156579566451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2992295627989750878843869 1122110860496156579566451)
          ·
            refine ⟨1683166290744234869349677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122110860496156579566451 1683166290744234869349677)
            ·
              refine ⟨631187359029088076006129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1683166290744234869349677 631187359029088076006129)
              ·
                refine ⟨473390519271816057004597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631187359029088076006129 473390519271816057004597)
                ·
                  refine ⟨44380361181732755344181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 473390519271816057004597 44380361181732755344181)
                  ·
                    rfl

theorem cell23_777874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_777874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777874 prefixEnd_777874 := by exact prefixLift 777874
  have htrace : WordTrace (prefixWord ++ tailWord_777874) baseStart_777874 baseEnd_777874 := by
    simpa [prefixWord, tailWord_777874, baseEnd_777874] using wordTrace_append hprefix tailTrace_777874
  have hstable : (prefixWord ++ tailWord_777874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777874).length < 2 ^ (prefixWord ++ tailWord_777874).sum := by decide
  have hdescent : baseEnd_777874 < baseStart_777874 := by decide
  rcases family_descends (prefixWord ++ tailWord_777874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777893 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_777893 : Nat := 118140960795 + 777893 * 2 ^ 59
def prefixEnd_777893 : Nat := 4983230072969 + 3 ^ 40 * 777893 * 2
def baseEnd_777893 : Nat := 399433006768030223760041

theorem tailTrace_777893 : CollatzResearch.WordTrace tailWord_777893 prefixEnd_777893 399433006768030223760041 := by
  unfold tailWord_777893
  simp only [CollatzResearch.WordTrace]
  refine ⟨28372088570833989392498333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18914725713889326261665555 28372088570833989392498333)
  ·
    refine ⟨10639533214062746022186875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28372088570833989392498333 10639533214062746022186875)
    ·
      refine ⟨15959299821094119033280313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10639533214062746022186875 15959299821094119033280313)
      ·
        refine ⟨11969474865820589274960235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15959299821094119033280313 11969474865820589274960235)
        ·
          refine ⟨17954212298730883912440353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11969474865820589274960235 17954212298730883912440353)
          ·
            refine ⟨13465659224048162934330265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17954212298730883912440353 13465659224048162934330265)
            ·
              refine ⟨10099244418036122200747699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13465659224048162934330265 10099244418036122200747699)
              ·
                refine ⟨15148866627054183301121549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10099244418036122200747699 15148866627054183301121549)
                ·
                  refine ⟨5680824985145318737920581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15148866627054183301121549 5680824985145318737920581)
                  ·
                    refine ⟨1065154684714747263360109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5680824985145318737920581 1065154684714747263360109)
                    ·
                      refine ⟨399433006768030223760041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1065154684714747263360109 399433006768030223760041)
                      ·
                        rfl

theorem cell23_777893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_777893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777893 prefixEnd_777893 := by exact prefixLift 777893
  have htrace : WordTrace (prefixWord ++ tailWord_777893) baseStart_777893 baseEnd_777893 := by
    simpa [prefixWord, tailWord_777893, baseEnd_777893] using wordTrace_append hprefix tailTrace_777893
  have hstable : (prefixWord ++ tailWord_777893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777893).length < 2 ^ (prefixWord ++ tailWord_777893).sum := by decide
  have hdescent : baseEnd_777893 < baseStart_777893 := by decide
  rcases family_descends (prefixWord ++ tailWord_777893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777917 : List Nat := [1, 4, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_777917 : Nat := 118140960795 + 777917 * 2 ^ 59
def prefixEnd_777917 : Nat := 4983230072969 + 3 ^ 40 * 777917 * 2
def baseEnd_777917 : Nat := 133148443434579376619977

theorem tailTrace_777917 : CollatzResearch.WordTrace tailWord_777917 prefixEnd_777917 133148443434579376619977 := by
  unfold tailWord_777917
  simp only [CollatzResearch.WordTrace]
  refine ⟨28372963922747041491372005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18915309281831360994248003 28372963922747041491372005)
  ·
    refine ⟨5319930735515070279632251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28372963922747041491372005 5319930735515070279632251)
    ·
      refine ⟨7979896103272605419448377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5319930735515070279632251 7979896103272605419448377)
      ·
        refine ⟨5984922077454454064586283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7979896103272605419448377 5984922077454454064586283)
        ·
          refine ⟨8977383116181681096879425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5984922077454454064586283 8977383116181681096879425)
          ·
            refine ⟨6733037337136260822659569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8977383116181681096879425 6733037337136260822659569)
            ·
              refine ⟨5049778002852195616994677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6733037337136260822659569 5049778002852195616994677)
              ·
                refine ⟨473416687767393339093251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5049778002852195616994677 473416687767393339093251)
                ·
                  refine ⟨710125031651090008639877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473416687767393339093251 710125031651090008639877)
                  ·
                    refine ⟨133148443434579376619977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 710125031651090008639877 133148443434579376619977)
                    ·
                      rfl

theorem cell23_777917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_777917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777917 prefixEnd_777917 := by exact prefixLift 777917
  have htrace : WordTrace (prefixWord ++ tailWord_777917) baseStart_777917 baseEnd_777917 := by
    simpa [prefixWord, tailWord_777917, baseEnd_777917] using wordTrace_append hprefix tailTrace_777917
  have hstable : (prefixWord ++ tailWord_777917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777917).length < 2 ^ (prefixWord ++ tailWord_777917).sum := by decide
  have hdescent : baseEnd_777917 < baseStart_777917 := by decide
  rcases family_descends (prefixWord ++ tailWord_777917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777943 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 5, 5]
def baseStart_777943 : Nat := 118140960795 + 777943 * 2 ^ 59
def prefixEnd_777943 : Nat := 4983230072969 + 3 ^ 40 * 777943 * 2
def baseEnd_777943 : Nat := 133152893600251676044937

theorem tailTrace_777943 : CollatzResearch.WordTrace tailWord_777943 prefixEnd_777943 133152893600251676044937 := by
  unfold tailWord_777943
  simp only [CollatzResearch.WordTrace]
  refine ⟨28373912220652847931818483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18915941480435231954545655 28373912220652847931818483)
  ·
    refine ⟨42560868330979271897727725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28373912220652847931818483 42560868330979271897727725)
    ·
      refine ⟨15960325624117226961647897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42560868330979271897727725 15960325624117226961647897)
      ·
        refine ⟨11970244218087920221235923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15960325624117226961647897 11970244218087920221235923)
        ·
          refine ⟨17955366327131880331853885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11970244218087920221235923 17955366327131880331853885)
          ·
            refine ⟨6733262372674455124445207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17955366327131880331853885 6733262372674455124445207)
            ·
              refine ⟨10099893559011682686667811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6733262372674455124445207 10099893559011682686667811)
              ·
                refine ⟨15149840338517524030001717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10099893559011682686667811 15149840338517524030001717)
                ·
                  refine ⟨1420297531736017877812661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15149840338517524030001717 1420297531736017877812661)
                  ·
                    refine ⟨133152893600251676044937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1420297531736017877812661 133152893600251676044937)
                    ·
                      rfl

theorem cell23_777943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_777943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777943 prefixEnd_777943 := by exact prefixLift 777943
  have htrace : WordTrace (prefixWord ++ tailWord_777943) baseStart_777943 baseEnd_777943 := by
    simpa [prefixWord, tailWord_777943, baseEnd_777943] using wordTrace_append hprefix tailTrace_777943
  have hstable : (prefixWord ++ tailWord_777943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777943).length < 2 ^ (prefixWord ++ tailWord_777943).sum := by decide
  have hdescent : baseEnd_777943 < baseStart_777943 := by decide
  rcases family_descends (prefixWord ++ tailWord_777943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777957 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 3]
def baseStart_777957 : Nat := 118140960795 + 777957 * 2 ^ 59
def prefixEnd_777957 : Nat := 4983230072969 + 3 ^ 40 * 777957 * 2
def baseEnd_777957 : Nat := 399465869529917973359747

theorem tailTrace_777957 : CollatzResearch.WordTrace tailWord_777957 prefixEnd_777957 399465869529917973359747 := by
  unfold tailWord_777957
  simp only [CollatzResearch.WordTrace]
  refine ⟨28374422842602128322828125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18916281895068085548552083 28374422842602128322828125)
  ·
    refine ⟨10640408565975798121060547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28374422842602128322828125 10640408565975798121060547)
    ·
      refine ⟨15960612848963697181590821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10640408565975798121060547 15960612848963697181590821)
      ·
        refine ⟨2992614909180693221548279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15960612848963697181590821 2992614909180693221548279)
        ·
          refine ⟨4488922363771039832322419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2992614909180693221548279 4488922363771039832322419)
          ·
            refine ⟨6733383545656559748483629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4488922363771039832322419 6733383545656559748483629)
            ·
              refine ⟨2525018829621209905681361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6733383545656559748483629 2525018829621209905681361)
              ·
                refine ⟨1893764122215907429261021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2525018829621209905681361 1893764122215907429261021)
                ·
                  refine ⟨710161545830965285972883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1893764122215907429261021 710161545830965285972883)
                  ·
                    refine ⟨1065242318746447928959325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 710161545830965285972883 1065242318746447928959325)
                    ·
                      refine ⟨399465869529917973359747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1065242318746447928959325 399465869529917973359747)
                      ·
                        rfl

theorem cell23_777957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_777957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777957 prefixEnd_777957 := by exact prefixLift 777957
  have htrace : WordTrace (prefixWord ++ tailWord_777957) baseStart_777957 baseEnd_777957 := by
    simpa [prefixWord, tailWord_777957, baseEnd_777957] using wordTrace_append hprefix tailTrace_777957
  have hstable : (prefixWord ++ tailWord_777957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777957).length < 2 ^ (prefixWord ++ tailWord_777957).sum := by decide
  have hdescent : baseEnd_777957 < baseStart_777957 := by decide
  rcases family_descends (prefixWord ++ tailWord_777957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777960 : List Nat := [2, 1, 4, 1, 3, 1, 2, 1, 3, 5]
def baseStart_777960 : Nat := 118140960795 + 777960 * 2 ^ 59
def prefixEnd_777960 : Nat := 4983230072969 + 3 ^ 40 * 777960 * 2
def baseEnd_777960 : Nat := 133155803323960487207411

theorem tailTrace_777960 : CollatzResearch.WordTrace tailWord_777960 prefixEnd_777960 133155803323960487207411 := by
  unfold tailWord_777960
  simp only [CollatzResearch.WordTrace]
  refine ⟨14187266130795629917593667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18916354841060839890124889 14187266130795629917593667)
  ·
    refine ⟨21280899196193444876390501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14187266130795629917593667 21280899196193444876390501)
    ·
      refine ⟨3990168599286270914323219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21280899196193444876390501 3990168599286270914323219)
      ·
        refine ⟨5985252898929406371484829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3990168599286270914323219 5985252898929406371484829)
        ·
          refine ⟨2244469837098527389306811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5985252898929406371484829 2244469837098527389306811)
          ·
            refine ⟨3366704755647791083960217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244469837098527389306811 3366704755647791083960217)
            ·
              refine ⟨2525028566735843312970163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366704755647791083960217 2525028566735843312970163)
              ·
                refine ⟨3787542850103764969455245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525028566735843312970163 3787542850103764969455245)
                ·
                  refine ⟨1420328568788911863545717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3787542850103764969455245 1420328568788911863545717)
                  ·
                    refine ⟨133155803323960487207411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1420328568788911863545717 133155803323960487207411)
                    ·
                      rfl

theorem cell23_777960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_777960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777960 prefixEnd_777960 := by exact prefixLift 777960
  have htrace : WordTrace (prefixWord ++ tailWord_777960) baseStart_777960 baseEnd_777960 := by
    simpa [prefixWord, tailWord_777960, baseEnd_777960] using wordTrace_append hprefix tailTrace_777960
  have hstable : (prefixWord ++ tailWord_777960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777960).length < 2 ^ (prefixWord ++ tailWord_777960).sum := by decide
  have hdescent : baseEnd_777960 < baseStart_777960 := by decide
  rcases family_descends (prefixWord ++ tailWord_777960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_777993 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_777993 : Nat := 118140960795 + 777993 * 2 ^ 59
def prefixEnd_777993 : Nat := 4983230072969 + 3 ^ 40 * 777993 * 2
def baseEnd_777993 : Nat := 399484354833479832509581

theorem tailTrace_777993 : CollatzResearch.WordTrace tailWord_777993 prefixEnd_777993 399484354833479832509581 := by
  unfold tailWord_777993
  simp only [CollatzResearch.WordTrace]
  refine ⟨28375735870471706471138633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18917157246981137647425755 28375735870471706471138633)
  ·
    refine ⟨21281801902853779853353975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28375735870471706471138633 21281801902853779853353975)
    ·
      refine ⟨31922702854280669780030963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21281801902853779853353975 31922702854280669780030963)
      ·
        refine ⟨47884054281421004670046445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31922702854280669780030963 47884054281421004670046445)
        ·
          refine ⟨17956520355532876751267417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47884054281421004670046445 17956520355532876751267417)
          ·
            refine ⟨13467390266649657563450563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17956520355532876751267417 13467390266649657563450563)
            ·
              refine ⟨20201085399974486345175845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13467390266649657563450563 20201085399974486345175845)
              ·
                refine ⟨3787703512495216189720471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20201085399974486345175845 3787703512495216189720471)
                ·
                  refine ⟨5681555268742824284580707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787703512495216189720471 5681555268742824284580707)
                  ·
                    refine ⟨8522332903114236426871061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5681555268742824284580707 8522332903114236426871061)
                    ·
                      refine ⟨399484354833479832509581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8522332903114236426871061 399484354833479832509581)
                      ·
                        rfl

theorem cell23_777993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_777993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_777993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_777993 prefixEnd_777993 := by exact prefixLift 777993
  have htrace : WordTrace (prefixWord ++ tailWord_777993) baseStart_777993 baseEnd_777993 := by
    simpa [prefixWord, tailWord_777993, baseEnd_777993] using wordTrace_append hprefix tailTrace_777993
  have hstable : (prefixWord ++ tailWord_777993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_777993).length < 2 ^ (prefixWord ++ tailWord_777993).sum := by decide
  have hdescent : baseEnd_777993 < baseStart_777993 := by decide
  rcases family_descends (prefixWord ++ tailWord_777993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778007 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 1, 6]
def baseStart_778007 : Nat := 118140960795 + 778007 * 2 ^ 59
def prefixEnd_778007 : Nat := 4983230072969 + 3 ^ 40 * 778007 * 2
def baseEnd_778007 : Nat := 133163847854214259244839

theorem tailTrace_778007 : CollatzResearch.WordTrace tailWord_778007 prefixEnd_778007 133163847854214259244839 := by
  unfold tailWord_778007
  simp only [CollatzResearch.WordTrace]
  refine ⟨28376246492420986862148275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18917497661613991241432183 28376246492420986862148275)
  ·
    refine ⟨42564369738631480293222413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28376246492420986862148275 42564369738631480293222413)
    ·
      refine ⟨15961638651986805109958405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42564369738631480293222413 15961638651986805109958405)
      ·
        refine ⟨2992807247247525958117201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15961638651986805109958405 2992807247247525958117201)
        ·
          refine ⟨2244605435435644468587901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2992807247247525958117201 2244605435435644468587901)
          ·
            refine ⟨841727038288366675720463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2244605435435644468587901 841727038288366675720463)
            ·
              refine ⟨1262590557432550013580695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841727038288366675720463 1262590557432550013580695)
              ·
                refine ⟨1893885836148825020371043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1262590557432550013580695 1893885836148825020371043)
                ·
                  refine ⟨2840828754223237530556565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1893885836148825020371043 2840828754223237530556565)
                  ·
                    refine ⟨133163847854214259244839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2840828754223237530556565 133163847854214259244839)
                    ·
                      rfl

theorem cell23_778007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_778007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778007 prefixEnd_778007 := by exact prefixLift 778007
  have htrace : WordTrace (prefixWord ++ tailWord_778007) baseStart_778007 baseEnd_778007 := by
    simpa [prefixWord, tailWord_778007, baseEnd_778007] using wordTrace_append hprefix tailTrace_778007
  have hstable : (prefixWord ++ tailWord_778007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778007).length < 2 ^ (prefixWord ++ tailWord_778007).sum := by decide
  have hdescent : baseEnd_778007 < baseStart_778007 := by decide
  rcases family_descends (prefixWord ++ tailWord_778007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778010 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6]
def baseStart_778010 : Nat := 118140960795 + 778010 * 2 ^ 59
def prefixEnd_778010 : Nat := 4983230072969 + 3 ^ 40 * 778010 * 2
def baseEnd_778010 : Nat := 399493084004606265997003

theorem tailTrace_778010 : CollatzResearch.WordTrace tailWord_778010 prefixEnd_778010 399493084004606265997003 := by
  unfold tailWord_778010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7094088977852529593626871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18917570607606745583004989 7094088977852529593626871)
  ·
    refine ⟨10641133466778794390440307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7094088977852529593626871 10641133466778794390440307)
    ·
      refine ⟨15961700200168191585660461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10641133466778794390440307 15961700200168191585660461)
      ·
        refine ⟨5985637575063071844622673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15961700200168191585660461 5985637575063071844622673)
        ·
          refine ⟨4489228181297303883467005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5985637575063071844622673 4489228181297303883467005)
          ·
            refine ⟨1683460567986488956300127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4489228181297303883467005 1683460567986488956300127)
            ·
              refine ⟨2525190851979733434450191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683460567986488956300127 2525190851979733434450191)
              ·
                refine ⟨3787786277969600151675287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2525190851979733434450191 3787786277969600151675287)
                ·
                  refine ⟨5681679416954400227512931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3787786277969600151675287 5681679416954400227512931)
                  ·
                    refine ⟨8522519125431600341269397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5681679416954400227512931 8522519125431600341269397)
                    ·
                      refine ⟨399493084004606265997003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8522519125431600341269397 399493084004606265997003)
                      ·
                        rfl

theorem cell23_778010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_778010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778010 prefixEnd_778010 := by exact prefixLift 778010
  have htrace : WordTrace (prefixWord ++ tailWord_778010) baseStart_778010 baseEnd_778010 := by
    simpa [prefixWord, tailWord_778010, baseEnd_778010] using wordTrace_append hprefix tailTrace_778010
  have hstable : (prefixWord ++ tailWord_778010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778010).length < 2 ^ (prefixWord ++ tailWord_778010).sum := by decide
  have hdescent : baseEnd_778010 < baseStart_778010 := by decide
  rcases family_descends (prefixWord ++ tailWord_778010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778017 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_778017 : Nat := 118140960795 + 778017 * 2 ^ 59
def prefixEnd_778017 : Nat := 4983230072969 + 3 ^ 40 * 778017 * 2
def baseEnd_778017 : Nat := 399496678369187738609471

theorem tailTrace_778017 : CollatzResearch.WordTrace tailWord_778017 prefixEnd_778017 399496678369187738609471 := by
  unfold tailWord_778017
  simp only [CollatzResearch.WordTrace]
  refine ⟨28376611222384758570012305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18917740814923172380008203 28376611222384758570012305)
  ·
    refine ⟨21282458416788568927509229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28376611222384758570012305 21282458416788568927509229)
    ·
      refine ⟨7980921906295713347815961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21282458416788568927509229 7980921906295713347815961)
      ·
        refine ⟨5985691429721785010861971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7980921906295713347815961 5985691429721785010861971)
        ·
          refine ⟨8978537144582677516292957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5985691429721785010861971 8978537144582677516292957)
          ·
            refine ⟨3366951429218504068609859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8978537144582677516292957 3366951429218504068609859)
            ·
              refine ⟨5050427143827756102914789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3366951429218504068609859 5050427143827756102914789)
              ·
                refine ⟨946955089467704269296523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5050427143827756102914789 946955089467704269296523)
                ·
                  refine ⟨1420432634201556403944785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 946955089467704269296523 1420432634201556403944785)
                  ·
                    refine ⟨1065324475651167302958589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1420432634201556403944785 1065324475651167302958589)
                    ·
                      refine ⟨399496678369187738609471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1065324475651167302958589 399496678369187738609471)
                      ·
                        rfl

theorem cell23_778017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_778017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778017 prefixEnd_778017 := by exact prefixLift 778017
  have htrace : WordTrace (prefixWord ++ tailWord_778017) baseStart_778017 baseEnd_778017 := by
    simpa [prefixWord, tailWord_778017, baseEnd_778017] using wordTrace_append hprefix tailTrace_778017
  have hstable : (prefixWord ++ tailWord_778017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778017).length < 2 ^ (prefixWord ++ tailWord_778017).sum := by decide
  have hdescent : baseEnd_778017 < baseStart_778017 := by decide
  rcases family_descends (prefixWord ++ tailWord_778017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778020 : List Nat := [2, 3, 1, 3, 2, 2, 1, 9]
def baseStart_778020 : Nat := 118140960795 + 778020 * 2 ^ 59
def prefixEnd_778020 : Nat := 4983230072969 + 3 ^ 40 * 778020 * 2
def baseEnd_778020 : Nat := 14796230326338934328591

theorem tailTrace_778020 : CollatzResearch.WordTrace tailWord_778020 prefixEnd_778020 14796230326338934328591 := by
  unfold tailWord_778020
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188360320686945041185757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18917813760915926721581009 14188360320686945041185757)
  ·
    refine ⟨5320635120257604390444659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14188360320686945041185757 5320635120257604390444659)
    ·
      refine ⟨7980952680386406585666989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5320635120257604390444659 7980952680386406585666989)
      ·
        refine ⟨2992857255144902469625121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7980952680386406585666989 2992857255144902469625121)
        ·
          refine ⟨2244642941358676852218841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2992857255144902469625121 2244642941358676852218841)
          ·
            refine ⟨1683482206019007639164131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2244642941358676852218841 1683482206019007639164131)
            ·
              refine ⟨2525223309028511458746197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1683482206019007639164131 2525223309028511458746197)
              ·
                refine ⟨14796230326338934328591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2525223309028511458746197 14796230326338934328591)
                ·
                  rfl

theorem cell23_778020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 9].length) (baseStart_778020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778020 prefixEnd_778020 := by exact prefixLift 778020
  have htrace : WordTrace (prefixWord ++ tailWord_778020) baseStart_778020 baseEnd_778020 := by
    simpa [prefixWord, tailWord_778020, baseEnd_778020] using wordTrace_append hprefix tailTrace_778020
  have hstable : (prefixWord ++ tailWord_778020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778020).length < 2 ^ (prefixWord ++ tailWord_778020).sum := by decide
  have hdescent : baseEnd_778020 < baseStart_778020 := by decide
  rcases family_descends (prefixWord ++ tailWord_778020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778037 : List Nat := [1, 3, 3, 1, 5, 1, 9]
def baseStart_778037 : Nat := 118140960795 + 778037 * 2 ^ 59
def prefixEnd_778037 : Nat := 4983230072969 + 3 ^ 40 * 778037 * 2
def baseEnd_778037 : Nat := 4932184542991082226659

theorem tailTrace_778037 : CollatzResearch.WordTrace tailWord_778037 prefixEnd_778037 4932184542991082226659 := by
  unfold tailWord_778037
  simp only [CollatzResearch.WordTrace]
  refine ⟨28377340682312301985740365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18918227121541534657160243 28377340682312301985740365)
  ·
    refine ⟨10641502755867113244652637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28377340682312301985740365 10641502755867113244652637)
    ·
      refine ⟨3990563533450167466744739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10641502755867113244652637 3990563533450167466744739)
      ·
        refine ⟨5985845300175251200117109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3990563533450167466744739 5985845300175251200117109)
        ·
          refine ⟨561172996891429800010979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5985845300175251200117109 561172996891429800010979)
          ·
            refine ⟨841759495337144700016469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561172996891429800010979 841759495337144700016469)
            ·
              refine ⟨4932184542991082226659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 841759495337144700016469 4932184542991082226659)
              ·
                rfl

theorem cell23_778037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 9].length) (baseStart_778037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778037 prefixEnd_778037 := by exact prefixLift 778037
  have htrace : WordTrace (prefixWord ++ tailWord_778037) baseStart_778037 baseEnd_778037 := by
    simpa [prefixWord, tailWord_778037, baseEnd_778037] using wordTrace_append hprefix tailTrace_778037
  have hstable : (prefixWord ++ tailWord_778037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778037).length < 2 ^ (prefixWord ++ tailWord_778037).sum := by decide
  have hdescent : baseEnd_778037 < baseStart_778037 := by decide
  rcases family_descends (prefixWord ++ tailWord_778037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778054 : List Nat := [6, 1, 1, 2, 1, 2, 2, 8]
def baseStart_778054 : Nat := 118140960795 + 778054 * 2 ^ 59
def prefixEnd_778054 : Nat := 4983230072969 + 3 ^ 40 * 778054 * 2
def baseEnd_778054 : Nat := 14796876931607559031363

theorem tailTrace_778054 : CollatzResearch.WordTrace tailWord_778054 prefixEnd_778054 14796876931607559031363 := by
  unfold tailWord_778054
  simp only [CollatzResearch.WordTrace]
  refine ⟨886811272601584809034663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18918640482167142592739477 886811272601584809034663)
  ·
    refine ⟨1330216908902377213551995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 886811272601584809034663 1330216908902377213551995)
    ·
      refine ⟨1995325363353565820327993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330216908902377213551995 1995325363353565820327993)
      ·
        refine ⟨1496494022515174365245995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1995325363353565820327993 1496494022515174365245995)
        ·
          refine ⟨2244741033772761547868993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496494022515174365245995 2244741033772761547868993)
          ·
            refine ⟨1683555775329571160901745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2244741033772761547868993 1683555775329571160901745)
            ·
              refine ⟨1262666831497178370676309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1683555775329571160901745 1262666831497178370676309)
              ·
                refine ⟨14796876931607559031363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1262666831497178370676309 14796876931607559031363)
                ·
                  rfl

theorem cell23_778054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_778054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778054 prefixEnd_778054 := by exact prefixLift 778054
  have htrace : WordTrace (prefixWord ++ tailWord_778054) baseStart_778054 baseEnd_778054 := by
    simpa [prefixWord, tailWord_778054, baseEnd_778054] using wordTrace_append hprefix tailTrace_778054
  have hstable : (prefixWord ++ tailWord_778054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778054).length < 2 ^ (prefixWord ++ tailWord_778054).sum := by decide
  have hdescent : baseEnd_778054 < baseStart_778054 := by decide
  rcases family_descends (prefixWord ++ tailWord_778054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778057 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 3, 3, 2]
def baseStart_778057 : Nat := 118140960795 + 778057 * 2 ^ 59
def prefixEnd_778057 : Nat := 4983230072969 + 3 ^ 40 * 778057 * 2
def baseEnd_778057 : Nat := 399517217595367582109287

theorem tailTrace_778057 : CollatzResearch.WordTrace tailWord_778057 prefixEnd_778057 399517217595367582109287 := by
  unfold tailWord_778057
  simp only [CollatzResearch.WordTrace]
  refine ⟨28378070142239845401468425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18918713428159896934312283 28378070142239845401468425)
  ·
    refine ⟨21283552606679884051101319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28378070142239845401468425 21283552606679884051101319)
    ·
      refine ⟨31925328910019826076651979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21283552606679884051101319 31925328910019826076651979)
      ·
        refine ⟨47887993365029739114977969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31925328910019826076651979 47887993365029739114977969)
        ·
          refine ⟨35915995023772304336233477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47887993365029739114977969 35915995023772304336233477)
          ·
            refine ⟨6734249066957307063043777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35915995023772304336233477 6734249066957307063043777)
            ·
              refine ⟨5050686800217980297282833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6734249066957307063043777 5050686800217980297282833)
              ·
                refine ⟨3788015100163485222962125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5050686800217980297282833 3788015100163485222962125)
                ·
                  refine ⟨1420505662561306958610797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3788015100163485222962125 1420505662561306958610797)
                  ·
                    refine ⟨532689623460490109479049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1420505662561306958610797 532689623460490109479049)
                    ·
                      refine ⟨399517217595367582109287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532689623460490109479049 399517217595367582109287)
                      ·
                        rfl

theorem cell23_778057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 3, 2].length) (baseStart_778057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778057 prefixEnd_778057 := by exact prefixLift 778057
  have htrace : WordTrace (prefixWord ++ tailWord_778057) baseStart_778057 baseEnd_778057 := by
    simpa [prefixWord, tailWord_778057, baseEnd_778057] using wordTrace_append hprefix tailTrace_778057
  have hstable : (prefixWord ++ tailWord_778057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778057).length < 2 ^ (prefixWord ++ tailWord_778057).sum := by decide
  have hdescent : baseEnd_778057 < baseStart_778057 := by decide
  rcases family_descends (prefixWord ++ tailWord_778057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778142 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_778142 : Nat := 118140960795 + 778142 * 2 ^ 59
def prefixEnd_778142 : Nat := 4983230072969 + 3 ^ 40 * 778142 * 2
def baseEnd_778142 : Nat := 399560863450999749546397

theorem tailTrace_778142 : CollatzResearch.WordTrace tailWord_778142 prefixEnd_778142 399560863450999749546397 := by
  unfold tailWord_778142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3547646293366488114789085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18920780231287936612208453 3547646293366488114789085)
  ·
    refine ⟨1330367360012433043045907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3547646293366488114789085 1330367360012433043045907)
    ·
      refine ⟨1995551040018649564568861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330367360012433043045907 1995551040018649564568861)
      ·
        refine ⟨748331640006993586713323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1995551040018649564568861 748331640006993586713323)
        ·
          refine ⟨1122497460010490380069985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748331640006993586713323 1122497460010490380069985)
          ·
            refine ⟨841873095007867785052489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1122497460010490380069985 841873095007867785052489)
            ·
              refine ⟨631404821255900838789367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841873095007867785052489 631404821255900838789367)
              ·
                refine ⟨947107231883851258184051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631404821255900838789367 947107231883851258184051)
                ·
                  refine ⟨1420660847825776887276077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947107231883851258184051 1420660847825776887276077)
                  ·
                    refine ⟨532747817934666332728529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1420660847825776887276077 532747817934666332728529)
                    ·
                      refine ⟨399560863450999749546397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532747817934666332728529 399560863450999749546397)
                      ·
                        rfl

theorem cell23_778142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_778142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778142 prefixEnd_778142 := by exact prefixLift 778142
  have htrace : WordTrace (prefixWord ++ tailWord_778142) baseStart_778142 baseEnd_778142 := by
    simpa [prefixWord, tailWord_778142, baseEnd_778142] using wordTrace_append hprefix tailTrace_778142
  have hstable : (prefixWord ++ tailWord_778142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778142).length < 2 ^ (prefixWord ++ tailWord_778142).sum := by decide
  have hdescent : baseEnd_778142 < baseStart_778142 := by decide
  rcases family_descends (prefixWord ++ tailWord_778142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778187 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 3, 4]
def baseStart_778187 : Nat := 118140960795 + 778187 * 2 ^ 59
def prefixEnd_778187 : Nat := 4983230072969 + 3 ^ 40 * 778187 * 2
def baseEnd_778187 : Nat := 133194656693484024494563

theorem tailTrace_778187 : CollatzResearch.WordTrace tailWord_778187 prefixEnd_778187 133194656693484024494563 := by
  unfold tailWord_778187
  simp only [CollatzResearch.WordTrace]
  refine ⟨28382811631768877603700815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18921874421179251735800543 28382811631768877603700815)
  ·
    refine ⟨42574217447653316405551223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28382811631768877603700815 42574217447653316405551223)
    ·
      refine ⟨63861326171479974608326835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42574217447653316405551223 63861326171479974608326835)
      ·
        refine ⟨95791989257219961912490253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63861326171479974608326835 95791989257219961912490253)
        ·
          refine ⟨35921995971457485717183845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95791989257219961912490253 35921995971457485717183845)
          ·
            refine ⟨6735374244648278571971971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35921995971457485717183845 6735374244648278571971971)
            ·
              refine ⟨10103061366972417857957957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6735374244648278571971971 10103061366972417857957957)
              ·
                refine ⟨1894324006307328348367117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10103061366972417857957957 1894324006307328348367117)
                ·
                  refine ⟨710371502365248130637669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1894324006307328348367117 710371502365248130637669)
                  ·
                    refine ⟨133194656693484024494563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 710371502365248130637669 133194656693484024494563)
                    ·
                      rfl

theorem cell23_778187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 4].length) (baseStart_778187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778187 prefixEnd_778187 := by exact prefixLift 778187
  have htrace : WordTrace (prefixWord ++ tailWord_778187) baseStart_778187 baseEnd_778187 := by
    simpa [prefixWord, tailWord_778187, baseEnd_778187] using wordTrace_append hprefix tailTrace_778187
  have hstable : (prefixWord ++ tailWord_778187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778187).length < 2 ^ (prefixWord ++ tailWord_778187).sum := by decide
  have hdescent : baseEnd_778187 < baseStart_778187 := by decide
  rcases family_descends (prefixWord ++ tailWord_778187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778200 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 10]
def baseStart_778200 : Nat := 118140960795 + 778200 * 2 ^ 59
def prefixEnd_778200 : Nat := 4983230072969 + 3 ^ 40 * 778200 * 2
def baseEnd_778200 : Nat := 44398960592106724735681

theorem tailTrace_778200 : CollatzResearch.WordTrace tailWord_778200 prefixEnd_778200 44398960592106724735681 := by
  unfold tailWord_778200
  simp only [CollatzResearch.WordTrace]
  refine ⟨14191642890360890411962027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18922190520481187215949369 14191642890360890411962027)
  ·
    refine ⟨21287464335541335617943041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14191642890360890411962027 21287464335541335617943041)
    ·
      refine ⟨15965598251656001713457281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21287464335541335617943041 15965598251656001713457281)
      ·
        refine ⟨11974198688742001285092961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15965598251656001713457281 11974198688742001285092961)
        ·
          refine ⟨8980649016556500963819721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11974198688742001285092961 8980649016556500963819721)
          ·
            refine ⟨6735486762417375722864791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8980649016556500963819721 6735486762417375722864791)
            ·
              refine ⟨10103230143626063584297187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6735486762417375722864791 10103230143626063584297187)
              ·
                refine ⟨15154845215439095376445781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10103230143626063584297187 15154845215439095376445781)
                ·
                  refine ⟨44398960592106724735681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 15154845215439095376445781 44398960592106724735681)
                  ·
                    rfl

theorem cell23_778200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 10].length) (baseStart_778200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778200 prefixEnd_778200 := by exact prefixLift 778200
  have htrace : WordTrace (prefixWord ++ tailWord_778200) baseStart_778200 baseEnd_778200 := by
    simpa [prefixWord, tailWord_778200, baseEnd_778200] using wordTrace_append hprefix tailTrace_778200
  have hstable : (prefixWord ++ tailWord_778200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778200).length < 2 ^ (prefixWord ++ tailWord_778200).sum := by decide
  have hdescent : baseEnd_778200 < baseStart_778200 := by decide
  rcases family_descends (prefixWord ++ tailWord_778200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778220 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_778220 : Nat := 118140960795 + 778220 * 2 ^ 59
def prefixEnd_778220 : Nat := 4983230072969 + 3 ^ 40 * 778220 * 2
def baseEnd_778220 : Nat := 399600914942050444371037

theorem tailTrace_778220 : CollatzResearch.WordTrace tailWord_778220 prefixEnd_778220 399600914942050444371037 := by
  unfold tailWord_778220
  simp only [CollatzResearch.WordTrace]
  refine ⟨14192007620324662119826057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18922676827099549493101409 14192007620324662119826057)
  ·
    refine ⟨10644005715243496589869543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14192007620324662119826057 10644005715243496589869543)
    ·
      refine ⟨15966008572865244884804315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10644005715243496589869543 15966008572865244884804315)
      ·
        refine ⟨23949012859297867327206473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15966008572865244884804315 23949012859297867327206473)
        ·
          refine ⟨17961759644473400495404855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23949012859297867327206473 17961759644473400495404855)
          ·
            refine ⟨26942639466710100743107283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17961759644473400495404855 26942639466710100743107283)
            ·
              refine ⟨40413959200065151114660925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26942639466710100743107283 40413959200065151114660925)
              ·
                refine ⟨15155234700024431667997847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40413959200065151114660925 15155234700024431667997847)
                ·
                  refine ⟨22732852050036647501996771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15155234700024431667997847 22732852050036647501996771)
                  ·
                    refine ⟨34099278075054971252995157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22732852050036647501996771 34099278075054971252995157)
                    ·
                      refine ⟨399600914942050444371037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 34099278075054971252995157 399600914942050444371037)
                      ·
                        rfl

theorem cell23_778220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_778220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778220 prefixEnd_778220 := by exact prefixLift 778220
  have htrace : WordTrace (prefixWord ++ tailWord_778220) baseStart_778220 baseEnd_778220 := by
    simpa [prefixWord, tailWord_778220, baseEnd_778220] using wordTrace_append hprefix tailTrace_778220
  have hstable : (prefixWord ++ tailWord_778220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778220).length < 2 ^ (prefixWord ++ tailWord_778220).sum := by decide
  have hdescent : baseEnd_778220 < baseStart_778220 := by decide
  rcases family_descends (prefixWord ++ tailWord_778220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778240 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 7]
def baseStart_778240 : Nat := 118140960795 + 778240 * 2 ^ 59
def prefixEnd_778240 : Nat := 4983230072969 + 3 ^ 40 * 778240 * 2
def baseEnd_778240 : Nat := 399611184555140366120945

theorem tailTrace_778240 : CollatzResearch.WordTrace tailWord_778240 prefixEnd_778240 399611184555140366120945 := by
  unfold tailWord_778240
  simp only [CollatzResearch.WordTrace]
  refine ⟨14192372350288433827690087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18923163133717911770253449 14192372350288433827690087)
  ·
    refine ⟨21288558525432650741535131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14192372350288433827690087 21288558525432650741535131)
    ·
      refine ⟨31932837788148976112302697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21288558525432650741535131 31932837788148976112302697)
      ·
        refine ⟨23949628341111732084227023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31932837788148976112302697 23949628341111732084227023)
        ·
          refine ⟨35924442511667598126340535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23949628341111732084227023 35924442511667598126340535)
          ·
            refine ⟨53886663767501397189510803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35924442511667598126340535 53886663767501397189510803)
            ·
              refine ⟨80829995651252095784266205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53886663767501397189510803 80829995651252095784266205)
              ·
                refine ⟨30311248369219535919099827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80829995651252095784266205 30311248369219535919099827)
                ·
                  refine ⟨45466872553829303878649741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30311248369219535919099827 45466872553829303878649741)
                  ·
                    refine ⟨17050077207685988954493653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45466872553829303878649741 17050077207685988954493653)
                    ·
                      refine ⟨399611184555140366120945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17050077207685988954493653 399611184555140366120945)
                      ·
                        rfl

theorem cell23_778240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_778240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778240 prefixEnd_778240 := by exact prefixLift 778240
  have htrace : WordTrace (prefixWord ++ tailWord_778240) baseStart_778240 baseEnd_778240 := by
    simpa [prefixWord, tailWord_778240, baseEnd_778240] using wordTrace_append hprefix tailTrace_778240
  have hstable : (prefixWord ++ tailWord_778240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778240).length < 2 ^ (prefixWord ++ tailWord_778240).sum := by decide
  have hdescent : baseEnd_778240 < baseStart_778240 := by decide
  rcases family_descends (prefixWord ++ tailWord_778240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778304 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 3]
def baseStart_778304 : Nat := 118140960795 + 778304 * 2 ^ 59
def prefixEnd_778304 : Nat := 4983230072969 + 3 ^ 40 * 778304 * 2
def baseEnd_778304 : Nat := 399644047317028115720651

theorem tailTrace_778304 : CollatzResearch.WordTrace tailWord_778304 prefixEnd_778304 399644047317028115720651 := by
  unfold tailWord_778304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14193539486172503292854983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18924719314896671057139977 14193539486172503292854983)
  ·
    refine ⟨21290309229258754939282475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14193539486172503292854983 21290309229258754939282475)
    ·
      refine ⟨31935463843888132408923713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21290309229258754939282475 31935463843888132408923713)
      ·
        refine ⟨23951597882916099306692785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31935463843888132408923713 23951597882916099306692785)
        ·
          refine ⟨17963698412187074480019589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23951597882916099306692785 17963698412187074480019589)
          ·
            refine ⟨3368193452285076465003673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17963698412187074480019589 3368193452285076465003673)
            ·
              refine ⟨2526145089213807348752755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3368193452285076465003673 2526145089213807348752755)
              ·
                refine ⟨3789217633820711023129133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526145089213807348752755 3789217633820711023129133)
                ·
                  refine ⟨1420956612682766633673425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3789217633820711023129133 1420956612682766633673425)
                  ·
                    refine ⟨1065717459512074975255069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1420956612682766633673425 1065717459512074975255069)
                    ·
                      refine ⟨399644047317028115720651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1065717459512074975255069 399644047317028115720651)
                      ·
                        rfl

theorem cell23_778304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_778304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778304 prefixEnd_778304 := by exact prefixLift 778304
  have htrace : WordTrace (prefixWord ++ tailWord_778304) baseStart_778304 baseEnd_778304 := by
    simpa [prefixWord, tailWord_778304, baseEnd_778304] using wordTrace_append hprefix tailTrace_778304
  have hstable : (prefixWord ++ tailWord_778304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778304).length < 2 ^ (prefixWord ++ tailWord_778304).sum := by decide
  have hdescent : baseEnd_778304 < baseStart_778304 := by decide
  rcases family_descends (prefixWord ++ tailWord_778304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778318 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4]
def baseStart_778318 : Nat := 118140960795 + 778318 * 2 ^ 59
def prefixEnd_778318 : Nat := 4983230072969 + 3 ^ 40 * 778318 * 2
def baseEnd_778318 : Nat := 399651236046191060945587

theorem tailTrace_778318 : CollatzResearch.WordTrace tailWord_778318 prefixEnd_778318 399651236046191060945587 := by
  unfold tailWord_778318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3548448699286785872089951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18925059729529524651146405 3548448699286785872089951)
  ·
    refine ⟨5322673048930178808134927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3548448699286785872089951 5322673048930178808134927)
    ·
      refine ⟨7984009573395268212202391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5322673048930178808134927 7984009573395268212202391)
      ·
        refine ⟨11976014360092902318303587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7984009573395268212202391 11976014360092902318303587)
        ·
          refine ⟨17964021540139353477455381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11976014360092902318303587 17964021540139353477455381)
          ·
            refine ⟨842063509694032194255721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17964021540139353477455381 842063509694032194255721)
            ·
              refine ⟨631547632270524145691791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842063509694032194255721 631547632270524145691791)
              ·
                refine ⟨947321448405786218537687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631547632270524145691791 947321448405786218537687)
                ·
                  refine ⟨1420982172608679327806531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947321448405786218537687 1420982172608679327806531)
                  ·
                    refine ⟨2131473258913018991709797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1420982172608679327806531 2131473258913018991709797)
                    ·
                      refine ⟨399651236046191060945587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2131473258913018991709797 399651236046191060945587)
                      ·
                        rfl

theorem cell23_778318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_778318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778318 prefixEnd_778318 := by exact prefixLift 778318
  have htrace : WordTrace (prefixWord ++ tailWord_778318) baseStart_778318 baseEnd_778318 := by
    simpa [prefixWord, tailWord_778318, baseEnd_778318] using wordTrace_append hprefix tailTrace_778318
  have hstable : (prefixWord ++ tailWord_778318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778318).length < 2 ^ (prefixWord ++ tailWord_778318).sum := by decide
  have hdescent : baseEnd_778318 < baseStart_778318 := by decide
  rcases family_descends (prefixWord ++ tailWord_778318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778351 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 3]
def baseStart_778351 : Nat := 118140960795 + 778351 * 2 ^ 59
def prefixEnd_778351 : Nat := 4983230072969 + 3 ^ 40 * 778351 * 2
def baseEnd_778351 : Nat := 399668180907789431832935

theorem tailTrace_778351 : CollatzResearch.WordTrace tailWord_778351 prefixEnd_778351 399668180907789431832935 := by
  unfold tailWord_778351
  simp only [CollatzResearch.WordTrace]
  refine ⟨28388793203174733612670907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18925862135449822408447271 28388793203174733612670907)
  ·
    refine ⟨42583189804762100419006361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28388793203174733612670907 42583189804762100419006361)
    ·
      refine ⟨31937392353571575314254771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42583189804762100419006361 31937392353571575314254771)
      ·
        refine ⟨47906088530357362971382157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31937392353571575314254771 47906088530357362971382157)
        ·
          refine ⟨17964783198884011114268309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47906088530357362971382157 17964783198884011114268309)
          ·
            refine ⟨842099212447688020981327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17964783198884011114268309 842099212447688020981327)
            ·
              refine ⟨1263148818671532031471991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842099212447688020981327 1263148818671532031471991)
              ·
                refine ⟨1894723228007298047207987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263148818671532031471991 1894723228007298047207987)
                ·
                  refine ⟨2842084842010947070811981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1894723228007298047207987 2842084842010947070811981)
                  ·
                    refine ⟨1065781815754105151554493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2842084842010947070811981 1065781815754105151554493)
                    ·
                      refine ⟨399668180907789431832935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1065781815754105151554493 399668180907789431832935)
                      ·
                        rfl

theorem cell23_778351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 3, 3].length) (baseStart_778351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778351 prefixEnd_778351 := by exact prefixLift 778351
  have htrace : WordTrace (prefixWord ++ tailWord_778351) baseStart_778351 baseEnd_778351 := by
    simpa [prefixWord, tailWord_778351, baseEnd_778351] using wordTrace_append hprefix tailTrace_778351
  have hstable : (prefixWord ++ tailWord_778351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778351).length < 2 ^ (prefixWord ++ tailWord_778351).sum := by decide
  have hdescent : baseEnd_778351 < baseStart_778351 := by decide
  rcases family_descends (prefixWord ++ tailWord_778351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778369 : List Nat := [1, 2, 4, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_778369 : Nat := 118140960795 + 778369 * 2 ^ 59
def prefixEnd_778369 : Nat := 4983230072969 + 3 ^ 40 * 778369 * 2
def baseEnd_778369 : Nat := 399677423559570361407853

theorem tailTrace_778369 : CollatzResearch.WordTrace tailWord_778369 prefixEnd_778369 399677423559570361407853 := by
  unfold tailWord_778369
  simp only [CollatzResearch.WordTrace]
  refine ⟨28389449717109522686826161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18926299811406348457884107 28389449717109522686826161)
  ·
    refine ⟨21292087287832142015119621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28389449717109522686826161 21292087287832142015119621)
    ·
      refine ⟨3992266366468526627834929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21292087287832142015119621 3992266366468526627834929)
      ·
        refine ⟨2994199774851394970876197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3992266366468526627834929 2994199774851394970876197)
        ·
          refine ⟨561412457784636557039287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2994199774851394970876197 561412457784636557039287)
          ·
            refine ⟨842118686676954835558931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561412457784636557039287 842118686676954835558931)
            ·
              refine ⟨1263178030015432253338397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842118686676954835558931 1263178030015432253338397)
              ·
                refine ⟨473691761255787095001899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1263178030015432253338397 473691761255787095001899)
                ·
                  refine ⟨710537641883680642502849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473691761255787095001899 710537641883680642502849)
                  ·
                    refine ⟨532903231412760481877137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 710537641883680642502849 532903231412760481877137)
                    ·
                      refine ⟨399677423559570361407853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532903231412760481877137 399677423559570361407853)
                      ·
                        rfl

theorem cell23_778369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_778369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778369 prefixEnd_778369 := by exact prefixLift 778369
  have htrace : WordTrace (prefixWord ++ tailWord_778369) baseStart_778369 baseEnd_778369 := by
    simpa [prefixWord, tailWord_778369, baseEnd_778369] using wordTrace_append hprefix tailTrace_778369
  have hstable : (prefixWord ++ tailWord_778369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778369).length < 2 ^ (prefixWord ++ tailWord_778369).sum := by decide
  have hdescent : baseEnd_778369 < baseStart_778369 := by decide
  rcases family_descends (prefixWord ++ tailWord_778369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778378 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_778378 : Nat := 118140960795 + 778378 * 2 ^ 59
def prefixEnd_778378 : Nat := 4983230072969 + 3 ^ 40 * 778378 * 2
def baseEnd_778378 : Nat := 399682044885460826195311

theorem tailTrace_778378 : CollatzResearch.WordTrace tailWord_778378 prefixEnd_778378 399682044885460826195311 := by
  unfold tailWord_778378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097444493519229305975947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18926518649384611482602525 7097444493519229305975947)
  ·
    refine ⟨10646166740278843958963921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7097444493519229305975947 10646166740278843958963921)
    ·
      refine ⟨7984625055209132969222941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10646166740278843958963921 7984625055209132969222941)
      ·
        refine ⟨2994234395703424863458603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7984625055209132969222941 2994234395703424863458603)
        ·
          refine ⟨4491351593555137295187905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2994234395703424863458603 4491351593555137295187905)
          ·
            refine ⟨3368513695166352971390929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4491351593555137295187905 3368513695166352971390929)
            ·
              refine ⟨2526385271374764728543197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3368513695166352971390929 2526385271374764728543197)
              ·
                refine ⟨947394476765536773203699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2526385271374764728543197 947394476765536773203699)
                ·
                  refine ⟨1421091715148305159805549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947394476765536773203699 1421091715148305159805549)
                  ·
                    refine ⟨532909393180614434927081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1421091715148305159805549 532909393180614434927081)
                    ·
                      refine ⟨399682044885460826195311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 532909393180614434927081 399682044885460826195311)
                      ·
                        rfl

theorem cell23_778378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_778378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778378 prefixEnd_778378 := by exact prefixLift 778378
  have htrace : WordTrace (prefixWord ++ tailWord_778378) baseStart_778378 baseEnd_778378 := by
    simpa [prefixWord, tailWord_778378, baseEnd_778378] using wordTrace_append hprefix tailTrace_778378
  have hstable : (prefixWord ++ tailWord_778378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778378).length < 2 ^ (prefixWord ++ tailWord_778378).sum := by decide
  have hdescent : baseEnd_778378 < baseStart_778378 := by decide
  rcases family_descends (prefixWord ++ tailWord_778378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778402 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 2, 1, 3]
def baseStart_778402 : Nat := 118140960795 + 778402 * 2 ^ 59
def prefixEnd_778402 : Nat := 4983230072969 + 3 ^ 40 * 778402 * 2
def baseEnd_778402 : Nat := 399694368421168732295201

theorem tailTrace_778402 : CollatzResearch.WordTrace tailWord_778402 prefixEnd_778402 399694368421168732295201 := by
  unfold tailWord_778402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7097663331497492330694365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18927102217326646215184973 7097663331497492330694365)
  ·
    refine ⟨2661623749311559624010387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7097663331497492330694365 2661623749311559624010387)
    ·
      refine ⟨3992435623967339436015581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2661623749311559624010387 3992435623967339436015581)
      ·
        refine ⟨1497163358987752288505843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3992435623967339436015581 1497163358987752288505843)
        ·
          refine ⟨2245745038481628432758765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497163358987752288505843 2245745038481628432758765)
          ·
            refine ⟨842154389430610662284537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2245745038481628432758765 842154389430610662284537)
            ·
              refine ⟨631615792072957996713403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842154389430610662284537 631615792072957996713403)
              ·
                refine ⟨947423688109436995070105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631615792072957996713403 947423688109436995070105)
                ·
                  refine ⟨710567766082077746302579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 947423688109436995070105 710567766082077746302579)
                  ·
                    refine ⟨1065851649123116619453869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 710567766082077746302579 1065851649123116619453869)
                    ·
                      refine ⟨399694368421168732295201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1065851649123116619453869 399694368421168732295201)
                      ·
                        rfl

theorem cell23_778402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_778402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778402 prefixEnd_778402 := by exact prefixLift 778402
  have htrace : WordTrace (prefixWord ++ tailWord_778402) baseStart_778402 baseEnd_778402 := by
    simpa [prefixWord, tailWord_778402, baseEnd_778402] using wordTrace_append hprefix tailTrace_778402
  have hstable : (prefixWord ++ tailWord_778402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778402).length < 2 ^ (prefixWord ++ tailWord_778402).sum := by decide
  have hdescent : baseEnd_778402 < baseStart_778402 := by decide
  rcases family_descends (prefixWord ++ tailWord_778402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778464 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 4]
def baseStart_778464 : Nat := 118140960795 + 778464 * 2 ^ 59
def prefixEnd_778464 : Nat := 4983230072969 + 3 ^ 40 * 778464 * 2
def baseEnd_778464 : Nat := 399726204221747489719915

theorem tailTrace_778464 : CollatzResearch.WordTrace tailWord_778464 prefixEnd_778464 399726204221747489719915 := by
  unfold tailWord_778464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14196457325882676955767223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18928609767843569274356297 14196457325882676955767223)
  ·
    refine ⟨21294685988824015433650835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14196457325882676955767223 21294685988824015433650835)
    ·
      refine ⟨31942028983236023150476253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21294685988824015433650835 31942028983236023150476253)
      ·
        refine ⟨11978260868713508681428595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31942028983236023150476253 11978260868713508681428595)
        ·
          refine ⟨17967391303070263022142893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11978260868713508681428595 17967391303070263022142893)
          ·
            refine ⟨6737771738651348633303585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17967391303070263022142893 6737771738651348633303585)
            ·
              refine ⟨5053328803988511474977689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6737771738651348633303585 5053328803988511474977689)
              ·
                refine ⟨3789996602991383606233267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5053328803988511474977689 3789996602991383606233267)
                ·
                  refine ⟨5684994904487075409349901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3789996602991383606233267 5684994904487075409349901)
                  ·
                    refine ⟨2131873089182653278506213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5684994904487075409349901 2131873089182653278506213)
                    ·
                      refine ⟨399726204221747489719915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2131873089182653278506213 399726204221747489719915)
                      ·
                        rfl

theorem cell23_778464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_778464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778464 prefixEnd_778464 := by exact prefixLift 778464
  have htrace : WordTrace (prefixWord ++ tailWord_778464) baseStart_778464 baseEnd_778464 := by
    simpa [prefixWord, tailWord_778464, baseEnd_778464] using wordTrace_append hprefix tailTrace_778464
  have hstable : (prefixWord ++ tailWord_778464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778464).length < 2 ^ (prefixWord ++ tailWord_778464).sum := by decide
  have hdescent : baseEnd_778464 < baseStart_778464 := by decide
  rcases family_descends (prefixWord ++ tailWord_778464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778481 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_778481 : Nat := 118140960795 + 778481 * 2 ^ 59
def prefixEnd_778481 : Nat := 4983230072969 + 3 ^ 40 * 778481 * 2
def baseEnd_778481 : Nat := 399734933392873923207337

theorem tailTrace_778481 : CollatzResearch.WordTrace tailWord_778481 prefixEnd_778481 399734933392873923207337 := by
  unfold tailWord_778481
  simp only [CollatzResearch.WordTrace]
  refine ⟨28393534692703765814903297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18929023128469177209935531 28393534692703765814903297)
  ·
    refine ⟨21295151019527824361177473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28393534692703765814903297 21295151019527824361177473)
    ·
      refine ⟨15971363264645868270883105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21295151019527824361177473 15971363264645868270883105)
      ·
        refine ⟨11978522448484401203162329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15971363264645868270883105 11978522448484401203162329)
        ·
          refine ⟨8983891836363300902371747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11978522448484401203162329 8983891836363300902371747)
          ·
            refine ⟨13475837754544951353557621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8983891836363300902371747 13475837754544951353557621)
            ·
              refine ⟨1263359789488589189396027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13475837754544951353557621 1263359789488589189396027)
              ·
                refine ⟨1895039684232883784094041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263359789488589189396027 1895039684232883784094041)
                ·
                  refine ⟨1421279763174662838070531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1895039684232883784094041 1421279763174662838070531)
                  ·
                    refine ⟨2131919644761994257105797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1421279763174662838070531 2131919644761994257105797)
                    ·
                      refine ⟨399734933392873923207337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2131919644761994257105797 399734933392873923207337)
                      ·
                        rfl

theorem cell23_778481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_778481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778481 prefixEnd_778481 := by exact prefixLift 778481
  have htrace : WordTrace (prefixWord ++ tailWord_778481) baseStart_778481 baseEnd_778481 := by
    simpa [prefixWord, tailWord_778481, baseEnd_778481] using wordTrace_append hprefix tailTrace_778481
  have hstable : (prefixWord ++ tailWord_778481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778481).length < 2 ^ (prefixWord ++ tailWord_778481).sum := by decide
  have hdescent : baseEnd_778481 < baseStart_778481 := by decide
  rcases family_descends (prefixWord ++ tailWord_778481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778508 : List Nat := [2, 2, 1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_778508 : Nat := 118140960795 + 778508 * 2 ^ 59
def prefixEnd_778508 : Nat := 4983230072969 + 3 ^ 40 * 778508 * 2
def baseEnd_778508 : Nat := 133249599123515105856571

theorem tailTrace_778508 : CollatzResearch.WordTrace tailWord_778508 prefixEnd_778508 133249599123515105856571 := by
  unfold tailWord_778508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14197259731802974713068089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18929679642403966284090785 14197259731802974713068089)
  ·
    refine ⟨10647944798852231034801067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14197259731802974713068089 10647944798852231034801067)
    ·
      refine ⟨15971917198278346552201601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10647944798852231034801067 15971917198278346552201601)
      ·
        refine ⟨11978937898708759914151201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15971917198278346552201601 11978937898708759914151201)
        ·
          refine ⟨8984203424031569935613401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11978937898708759914151201 8984203424031569935613401)
          ·
            refine ⟨6738152568023677451710051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8984203424031569935613401 6738152568023677451710051)
            ·
              refine ⟨10107228852035516177565077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6738152568023677451710051 10107228852035516177565077)
              ·
                refine ⟨473776352439164820823363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10107228852035516177565077 473776352439164820823363)
                ·
                  refine ⟨710664528658747231235045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473776352439164820823363 710664528658747231235045)
                  ·
                    refine ⟨133249599123515105856571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 710664528658747231235045 133249599123515105856571)
                    ·
                      rfl

theorem cell23_778508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_778508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778508 prefixEnd_778508 := by exact prefixLift 778508
  have htrace : WordTrace (prefixWord ++ tailWord_778508) baseStart_778508 baseEnd_778508 := by
    simpa [prefixWord, tailWord_778508, baseEnd_778508] using wordTrace_append hprefix tailTrace_778508
  have hstable : (prefixWord ++ tailWord_778508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778508).length < 2 ^ (prefixWord ++ tailWord_778508).sum := by decide
  have hdescent : baseEnd_778508 < baseStart_778508 := by decide
  rcases family_descends (prefixWord ++ tailWord_778508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778524 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_778524 : Nat := 118140960795 + 778524 * 2 ^ 59
def prefixEnd_778524 : Nat := 4983230072969 + 3 ^ 40 * 778524 * 2
def baseEnd_778524 : Nat := 399757013061017254969639

theorem tailTrace_778524 : CollatzResearch.WordTrace tailWord_778524 prefixEnd_778524 399757013061017254969639 := by
  unfold tailWord_778524
  simp only [CollatzResearch.WordTrace]
  refine ⟨14197551515773992079359313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18930068687698656105812417 14197551515773992079359313)
  ·
    refine ⟨10648163636830494059519485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14197551515773992079359313 10648163636830494059519485)
    ·
      refine ⟨3993061363811435272319807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10648163636830494059519485 3993061363811435272319807)
      ·
        refine ⟨5989592045717152908479711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993061363811435272319807 5989592045717152908479711)
        ·
          refine ⟨8984388068575729362719567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5989592045717152908479711 8984388068575729362719567)
          ·
            refine ⟨13476582102863594044079351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8984388068575729362719567 13476582102863594044079351)
            ·
              refine ⟨20214873154295391066119027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13476582102863594044079351 20214873154295391066119027)
              ·
                refine ⟨30322309731443086599178541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20214873154295391066119027 30322309731443086599178541)
                ·
                  refine ⟨11370866149291157474691953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30322309731443086599178541 11370866149291157474691953)
                  ·
                    refine ⟨8528149611968368106018965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11370866149291157474691953 8528149611968368106018965)
                    ·
                      refine ⟨399757013061017254969639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8528149611968368106018965 399757013061017254969639)
                      ·
                        rfl

theorem cell23_778524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_778524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778524 prefixEnd_778524 := by exact prefixLift 778524
  have htrace : WordTrace (prefixWord ++ tailWord_778524) baseStart_778524 baseEnd_778524 := by
    simpa [prefixWord, tailWord_778524, baseEnd_778524] using wordTrace_append hprefix tailTrace_778524
  have hstable : (prefixWord ++ tailWord_778524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778524).length < 2 ^ (prefixWord ++ tailWord_778524).sum := by decide
  have hdescent : baseEnd_778524 < baseStart_778524 := by decide
  rcases family_descends (prefixWord ++ tailWord_778524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778571 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 2, 6, 2]
def baseStart_778571 : Nat := 118140960795 + 778571 * 2 ^ 59
def prefixEnd_778571 : Nat := 4983230072969 + 3 ^ 40 * 778571 * 2
def baseEnd_778571 : Nat := 399781146651778571081923

theorem tailTrace_778571 : CollatzResearch.WordTrace tailWord_778571 prefixEnd_778571 399781146651778571081923 := by
  unfold tailWord_778571
  simp only [CollatzResearch.WordTrace]
  refine ⟨28396817262377711185679567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18931211508251807457119711 28396817262377711185679567)
  ·
    refine ⟨42595225893566566778519351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28396817262377711185679567 42595225893566566778519351)
    ·
      refine ⟨63892838840349850167779027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42595225893566566778519351 63892838840349850167779027)
      ·
        refine ⟨95839258260524775251668541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63892838840349850167779027 95839258260524775251668541)
        ·
          refine ⟨35939721847696790719375703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95839258260524775251668541 35939721847696790719375703)
          ·
            refine ⟨53909582771545186079063555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35939721847696790719375703 53909582771545186079063555)
            ·
              refine ⟨80864374157317779118595333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53909582771545186079063555 80864374157317779118595333)
              ·
                refine ⟨15162070154497083584736625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80864374157317779118595333 15162070154497083584736625)
                ·
                  refine ⟨11371552615872812688552469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15162070154497083584736625 11371552615872812688552469)
                  ·
                    refine ⟨533041528869038094775897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11371552615872812688552469 533041528869038094775897)
                    ·
                      refine ⟨399781146651778571081923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533041528869038094775897 399781146651778571081923)
                      ·
                        rfl

theorem cell23_778571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 6, 2].length) (baseStart_778571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778571 prefixEnd_778571 := by exact prefixLift 778571
  have htrace : WordTrace (prefixWord ++ tailWord_778571) baseStart_778571 baseEnd_778571 := by
    simpa [prefixWord, tailWord_778571, baseEnd_778571] using wordTrace_append hprefix tailTrace_778571
  have hstable : (prefixWord ++ tailWord_778571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778571).length < 2 ^ (prefixWord ++ tailWord_778571).sum := by decide
  have hdescent : baseEnd_778571 < baseStart_778571 := by decide
  rcases family_descends (prefixWord ++ tailWord_778571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778601 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_778601 : Nat := 118140960795 + 778601 * 2 ^ 59
def prefixEnd_778601 : Nat := 4983230072969 + 3 ^ 40 * 778601 * 2
def baseEnd_778601 : Nat := 399796551071413453706785

theorem tailTrace_778601 : CollatzResearch.WordTrace tailWord_778601 prefixEnd_778601 399796551071413453706785 := by
  unfold tailWord_778601
  simp only [CollatzResearch.WordTrace]
  refine ⟨28397911452269026309271657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18931940968179350872847771 28397911452269026309271657)
  ·
    refine ⟨21298433589201769731953743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28397911452269026309271657 21298433589201769731953743)
    ·
      refine ⟨31947650383802654597930615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21298433589201769731953743 31947650383802654597930615)
      ·
        refine ⟨47921475575703981896895923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31947650383802654597930615 47921475575703981896895923)
        ·
          refine ⟨71882213363555972845343885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47921475575703981896895923 71882213363555972845343885)
          ·
            refine ⟨26955830011333489817003957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71882213363555972845343885 26955830011333489817003957)
            ·
              refine ⟨2527109063562514670344121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26955830011333489817003957 2527109063562514670344121)
              ·
                refine ⟨1895331797671886002758091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2527109063562514670344121 1895331797671886002758091)
                ·
                  refine ⟨2842997696507829004137137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895331797671886002758091 2842997696507829004137137)
                  ·
                    refine ⟨2132248272380871753102853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2842997696507829004137137 2132248272380871753102853)
                    ·
                      refine ⟨399796551071413453706785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2132248272380871753102853 399796551071413453706785)
                      ·
                        rfl

theorem cell23_778601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_778601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778601 prefixEnd_778601 := by exact prefixLift 778601
  have htrace : WordTrace (prefixWord ++ tailWord_778601) baseStart_778601 baseEnd_778601 := by
    simpa [prefixWord, tailWord_778601, baseEnd_778601] using wordTrace_append hprefix tailTrace_778601
  have hstable : (prefixWord ++ tailWord_778601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778601).length < 2 ^ (prefixWord ++ tailWord_778601).sum := by decide
  have hdescent : baseEnd_778601 < baseStart_778601 := by decide
  rcases family_descends (prefixWord ++ tailWord_778601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778605 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 1, 1, 4]
def baseStart_778605 : Nat := 118140960795 + 778605 * 2 ^ 59
def prefixEnd_778605 : Nat := 4983230072969 + 3 ^ 40 * 778605 * 2
def baseEnd_778605 : Nat := 399798604994031438056767

theorem tailTrace_778605 : CollatzResearch.WordTrace tailWord_778605 prefixEnd_778605 399798604994031438056767 := by
  unfold tailWord_778605
  simp only [CollatzResearch.WordTrace]
  refine ⟨28398057344254534992417269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18932038229503023328278179 28398057344254534992417269)
  ·
    refine ⟨2662317876023862655539119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28398057344254534992417269 2662317876023862655539119)
    ·
      refine ⟨3993476814035793983308679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2662317876023862655539119 3993476814035793983308679)
      ·
        refine ⟨5990215221053690974963019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3993476814035793983308679 5990215221053690974963019)
        ·
          refine ⟨8985322831580536462444529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5990215221053690974963019 8985322831580536462444529)
          ·
            refine ⟨6738992123685402346833397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8985322831580536462444529 6738992123685402346833397)
            ·
              refine ⟨631780511595506470015631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6738992123685402346833397 631780511595506470015631)
              ·
                refine ⟨947670767393259705023447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631780511595506470015631 947670767393259705023447)
                ·
                  refine ⟨1421506151089889557535171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947670767393259705023447 1421506151089889557535171)
                  ·
                    refine ⟨2132259226634834336302757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1421506151089889557535171 2132259226634834336302757)
                    ·
                      refine ⟨399798604994031438056767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2132259226634834336302757 399798604994031438056767)
                      ·
                        rfl

theorem cell23_778605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_778605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778605 prefixEnd_778605 := by exact prefixLift 778605
  have htrace : WordTrace (prefixWord ++ tailWord_778605) baseStart_778605 baseEnd_778605 := by
    simpa [prefixWord, tailWord_778605, baseEnd_778605] using wordTrace_append hprefix tailTrace_778605
  have hstable : (prefixWord ++ tailWord_778605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778605).length < 2 ^ (prefixWord ++ tailWord_778605).sum := by decide
  have hdescent : baseEnd_778605 < baseStart_778605 := by decide
  rcases family_descends (prefixWord ++ tailWord_778605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778608 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 5]
def baseStart_778608 : Nat := 118140960795 + 778608 * 2 ^ 59
def prefixEnd_778608 : Nat := 4983230072969 + 3 ^ 40 * 778608 * 2
def baseEnd_778608 : Nat := 399800145435994926319253

theorem tailTrace_778608 : CollatzResearch.WordTrace tailWord_778608 prefixEnd_778608 399800145435994926319253 := by
  unfold tailWord_778608
  simp only [CollatzResearch.WordTrace]
  refine ⟨14199083381621833252388239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18932111175495777669850985 14199083381621833252388239)
  ·
    refine ⟨21298625072432749878582359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14199083381621833252388239 21298625072432749878582359)
    ·
      refine ⟨31947937608649124817873539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21298625072432749878582359 31947937608649124817873539)
      ·
        refine ⟨47921906412973687226810309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31947937608649124817873539 47921906412973687226810309)
        ·
          refine ⟨8985357452432566355026933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47921906412973687226810309 8985357452432566355026933)
          ·
            refine ⟨842377261165553095783775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8985357452432566355026933 842377261165553095783775)
            ·
              refine ⟨1263565891748329643675663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842377261165553095783775 1263565891748329643675663)
              ·
                refine ⟨1895348837622494465513495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263565891748329643675663 1895348837622494465513495)
                ·
                  refine ⟨2843023256433741698270243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895348837622494465513495 2843023256433741698270243)
                  ·
                    refine ⟨4264534884650612547405365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2843023256433741698270243 4264534884650612547405365)
                    ·
                      refine ⟨399800145435994926319253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4264534884650612547405365 399800145435994926319253)
                      ·
                        rfl

theorem cell23_778608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 5].length) (baseStart_778608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778608 prefixEnd_778608 := by exact prefixLift 778608
  have htrace : WordTrace (prefixWord ++ tailWord_778608) baseStart_778608 baseEnd_778608 := by
    simpa [prefixWord, tailWord_778608, baseEnd_778608] using wordTrace_append hprefix tailTrace_778608
  have hstable : (prefixWord ++ tailWord_778608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778608).length < 2 ^ (prefixWord ++ tailWord_778608).sum := by decide
  have hdescent : baseEnd_778608 < baseStart_778608 := by decide
  rcases family_descends (prefixWord ++ tailWord_778608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778666 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 2, 4]
def baseStart_778666 : Nat := 118140960795 + 778666 * 2 ^ 59
def prefixEnd_778666 : Nat := 4983230072969 + 3 ^ 40 * 778666 * 2
def baseEnd_778666 : Nat := 133276642437985233131329

theorem tailTrace_778666 : CollatzResearch.WordTrace tailWord_778666 prefixEnd_778666 133276642437985233131329 := by
  unfold tailWord_778666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7100070549258385602596963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18933521464689028273591901 7100070549258385602596963)
  ·
    refine ⟨10650105823887578403895445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7100070549258385602596963 10650105823887578403895445)
    ·
      refine ⟨499223710494730237682599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10650105823887578403895445 499223710494730237682599)
      ·
        refine ⟨748835565742095356523899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499223710494730237682599 748835565742095356523899)
        ·
          refine ⟨1123253348613143034785849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748835565742095356523899 1123253348613143034785849)
          ·
            refine ⟨842440011459857276089387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123253348613143034785849 842440011459857276089387)
            ·
              refine ⟨1263660017189785914134081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842440011459857276089387 1263660017189785914134081)
              ·
                refine ⟨947745012892339435600561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1263660017189785914134081 947745012892339435600561)
                ·
                  refine ⟨710808759669254576700421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 947745012892339435600561 710808759669254576700421)
                  ·
                    refine ⟨133276642437985233131329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 710808759669254576700421 133276642437985233131329)
                    ·
                      rfl

theorem cell23_778666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_778666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778666 prefixEnd_778666 := by exact prefixLift 778666
  have htrace : WordTrace (prefixWord ++ tailWord_778666) baseStart_778666 baseEnd_778666 := by
    simpa [prefixWord, tailWord_778666, baseEnd_778666] using wordTrace_append hprefix tailTrace_778666
  have hstable : (prefixWord ++ tailWord_778666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778666).length < 2 ^ (prefixWord ++ tailWord_778666).sum := by decide
  have hdescent : baseEnd_778666 < baseStart_778666 := by decide
  rcases family_descends (prefixWord ++ tailWord_778666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778695 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_778695 : Nat := 118140960795 + 778695 * 2 ^ 59
def prefixEnd_778695 : Nat := 4983230072969 + 3 ^ 40 * 778695 * 2
def baseEnd_778695 : Nat := 399844818252936085931353

theorem tailTrace_778695 : CollatzResearch.WordTrace tailWord_778695 prefixEnd_778695 399844818252936085931353 := by
  unfold tailWord_778695
  simp only [CollatzResearch.WordTrace]
  refine ⟨28401339913928480363193539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18934226609285653575462359 28401339913928480363193539)
  ·
    refine ⟨42602009870892720544790309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28401339913928480363193539 42602009870892720544790309)
    ·
      refine ⟨7987876850792385102148183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42602009870892720544790309 7987876850792385102148183)
      ·
        refine ⟨11981815276188577653222275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7987876850792385102148183 11981815276188577653222275)
        ·
          refine ⟨17972722914282866479833413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11981815276188577653222275 17972722914282866479833413)
          ·
            refine ⟨3369885546428037464968765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17972722914282866479833413 3369885546428037464968765)
            ·
              refine ⟨1263707079910514049363287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3369885546428037464968765 1263707079910514049363287)
              ·
                refine ⟨1895560619865771074044931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263707079910514049363287 1895560619865771074044931)
                ·
                  refine ⟨2843340929798656611067397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1895560619865771074044931 2843340929798656611067397)
                  ·
                    refine ⟨533126424337248114575137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2843340929798656611067397 533126424337248114575137)
                    ·
                      refine ⟨399844818252936085931353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533126424337248114575137 399844818252936085931353)
                      ·
                        rfl

theorem cell23_778695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_778695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778695 prefixEnd_778695 := by exact prefixLift 778695
  have htrace : WordTrace (prefixWord ++ tailWord_778695) baseStart_778695 baseEnd_778695 := by
    simpa [prefixWord, tailWord_778695, baseEnd_778695] using wordTrace_append hprefix tailTrace_778695
  have hstable : (prefixWord ++ tailWord_778695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778695).length < 2 ^ (prefixWord ++ tailWord_778695).sum := by decide
  have hdescent : baseEnd_778695 < baseStart_778695 := by decide
  rcases family_descends (prefixWord ++ tailWord_778695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778785 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_778785 : Nat := 118140960795 + 778785 * 2 ^ 59
def prefixEnd_778785 : Nat := 4983230072969 + 3 ^ 40 * 778785 * 2
def baseEnd_778785 : Nat := 399891031511840733805939

theorem tailTrace_778785 : CollatzResearch.WordTrace tailWord_778785 prefixEnd_778785 399891031511840733805939 := by
  unfold tailWord_778785
  simp only [CollatzResearch.WordTrace]
  refine ⟨28404622483602425733969809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18936414989068283822646539 28404622483602425733969809)
  ·
    refine ⟨21303466862701819300477357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28404622483602425733969809 21303466862701819300477357)
    ·
      refine ⟨7988800073513182237679009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21303466862701819300477357 7988800073513182237679009)
      ·
        refine ⟨5991600055134886678259257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7988800073513182237679009 5991600055134886678259257)
        ·
          refine ⟨4493700041351165008694443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5991600055134886678259257 4493700041351165008694443)
          ·
            refine ⟨6740550062026747513041665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493700041351165008694443 6740550062026747513041665)
            ·
              refine ⟨5055412546520060634781249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6740550062026747513041665 5055412546520060634781249)
              ·
                refine ⟨3791559409890045476085937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5055412546520060634781249 3791559409890045476085937)
                ·
                  refine ⟨2843669557417534107064453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3791559409890045476085937 2843669557417534107064453)
                  ·
                    refine ⟨533188042015787645074585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2843669557417534107064453 533188042015787645074585)
                    ·
                      refine ⟨399891031511840733805939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533188042015787645074585 399891031511840733805939)
                      ·
                        rfl

theorem cell23_778785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_778785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778785 prefixEnd_778785 := by exact prefixLift 778785
  have htrace : WordTrace (prefixWord ++ tailWord_778785) baseStart_778785 baseEnd_778785 := by
    simpa [prefixWord, tailWord_778785, baseEnd_778785] using wordTrace_append hprefix tailTrace_778785
  have hstable : (prefixWord ++ tailWord_778785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778785).length < 2 ^ (prefixWord ++ tailWord_778785).sum := by decide
  have hdescent : baseEnd_778785 < baseStart_778785 := by decide
  rcases family_descends (prefixWord ++ tailWord_778785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778808 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 6]
def baseStart_778808 : Nat := 118140960795 + 778808 * 2 ^ 59
def prefixEnd_778808 : Nat := 4983230072969 + 3 ^ 40 * 778808 * 2
def baseEnd_778808 : Nat := 44433649062988238202037

theorem tailTrace_778808 : CollatzResearch.WordTrace tailWord_778808 prefixEnd_778808 44433649062988238202037 := by
  unfold tailWord_778808
  simp only [CollatzResearch.WordTrace]
  refine ⟨14202730681259550331028539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18936974241679400441371385 14202730681259550331028539)
  ·
    refine ⟨21304096021889325496542809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14202730681259550331028539 21304096021889325496542809)
    ·
      refine ⟨15978072016416994122407107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21304096021889325496542809 15978072016416994122407107)
      ·
        refine ⟨23967108024625491183610661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15978072016416994122407107 23967108024625491183610661)
        ·
          refine ⟨4493832754617279596926999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23967108024625491183610661 4493832754617279596926999)
          ·
            refine ⟨6740749131925919395390499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4493832754617279596926999 6740749131925919395390499)
            ·
              refine ⟨10111123697888879093085749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6740749131925919395390499 10111123697888879093085749)
              ·
                refine ⟨947917846677082414976789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10111123697888879093085749 947917846677082414976789)
                ·
                  refine ⟨44433649062988238202037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 947917846677082414976789 44433649062988238202037)
                  ·
                    rfl

theorem cell23_778808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 6].length) (baseStart_778808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778808 prefixEnd_778808 := by exact prefixLift 778808
  have htrace : WordTrace (prefixWord ++ tailWord_778808) baseStart_778808 baseEnd_778808 := by
    simpa [prefixWord, tailWord_778808, baseEnd_778808] using wordTrace_append hprefix tailTrace_778808
  have hstable : (prefixWord ++ tailWord_778808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778808).length < 2 ^ (prefixWord ++ tailWord_778808).sum := by decide
  have hdescent : baseEnd_778808 < baseStart_778808 := by decide
  rcases family_descends (prefixWord ++ tailWord_778808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778829 : List Nat := [1, 6, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_778829 : Nat := 118140960795 + 778829 * 2 ^ 59
def prefixEnd_778829 : Nat := 4983230072969 + 3 ^ 40 * 778829 * 2
def baseEnd_778829 : Nat := 133304541553546187218579

theorem tailTrace_778829 : CollatzResearch.WordTrace tailWord_778829 prefixEnd_778829 133304541553546187218579 := by
  unfold tailWord_778829
  simp only [CollatzResearch.WordTrace]
  refine ⟨28406227295443021248571541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18937484863628680832381027 28406227295443021248571541)
  ·
    refine ⟨1331541904473891621026791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28406227295443021248571541 1331541904473891621026791)
    ·
      refine ⟨1997312856710837431540187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1331541904473891621026791 1997312856710837431540187)
      ·
        refine ⟨2995969285066256147310281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997312856710837431540187 2995969285066256147310281)
        ·
          refine ⟨2246976963799692110482711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2995969285066256147310281 2246976963799692110482711)
          ·
            refine ⟨3370465445699538165724067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2246976963799692110482711 3370465445699538165724067)
            ·
              refine ⟨5055698168549307248586101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370465445699538165724067 5055698168549307248586101)
              ·
                refine ⟨473971703301497554554947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5055698168549307248586101 473971703301497554554947)
                ·
                  refine ⟨710957554952246331832421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473971703301497554554947 710957554952246331832421)
                  ·
                    refine ⟨133304541553546187218579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 710957554952246331832421 133304541553546187218579)
                    ·
                      rfl

theorem cell23_778829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_778829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778829 prefixEnd_778829 := by exact prefixLift 778829
  have htrace : WordTrace (prefixWord ++ tailWord_778829) baseStart_778829 baseEnd_778829 := by
    simpa [prefixWord, tailWord_778829, baseEnd_778829] using wordTrace_append hprefix tailTrace_778829
  have hstable : (prefixWord ++ tailWord_778829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778829).length < 2 ^ (prefixWord ++ tailWord_778829).sum := by decide
  have hdescent : baseEnd_778829 < baseStart_778829 := by decide
  rcases family_descends (prefixWord ++ tailWord_778829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778852 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_778852 : Nat := 118140960795 + 778852 * 2 ^ 59
def prefixEnd_778852 : Nat := 4983230072969 + 3 ^ 40 * 778852 * 2
def baseEnd_778852 : Nat := 399925434715691971668131

theorem tailTrace_778852 : CollatzResearch.WordTrace tailWord_778852 prefixEnd_778852 399925434715691971668131 := by
  unfold tailWord_778852
  simp only [CollatzResearch.WordTrace]
  refine ⟨14203533087179848088329405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18938044116239797451105873 14203533087179848088329405)
  ·
    refine ⟨5326324907692443033123527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14203533087179848088329405 5326324907692443033123527)
    ·
      refine ⟨7989487361538664549685291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5326324907692443033123527 7989487361538664549685291)
      ·
        refine ⟨11984231042307996824527937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7989487361538664549685291 11984231042307996824527937)
        ·
          refine ⟨8988173281730997618395953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11984231042307996824527937 8988173281730997618395953)
          ·
            refine ⟨6741129961298248213796965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8988173281730997618395953 6741129961298248213796965)
            ·
              refine ⟨1263961867743421540086931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6741129961298248213796965 1263961867743421540086931)
              ·
                refine ⟨1895942801615132310130397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1263961867743421540086931 1895942801615132310130397)
                ·
                  refine ⟨710978550605674616298899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1895942801615132310130397 710978550605674616298899)
                  ·
                    refine ⟨1066467825908511924448349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 710978550605674616298899 1066467825908511924448349)
                    ·
                      refine ⟨399925434715691971668131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1066467825908511924448349 399925434715691971668131)
                      ·
                        rfl

theorem cell23_778852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_778852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778852 prefixEnd_778852 := by exact prefixLift 778852
  have htrace : WordTrace (prefixWord ++ tailWord_778852) baseStart_778852 baseEnd_778852 := by
    simpa [prefixWord, tailWord_778852, baseEnd_778852] using wordTrace_append hprefix tailTrace_778852
  have hstable : (prefixWord ++ tailWord_778852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778852).length < 2 ^ (prefixWord ++ tailWord_778852).sum := by decide
  have hdescent : baseEnd_778852 < baseStart_778852 := by decide
  rcases family_descends (prefixWord ++ tailWord_778852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778862 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_778862 : Nat := 118140960795 + 778862 * 2 ^ 59
def prefixEnd_778862 : Nat := 4983230072969 + 3 ^ 40 * 778862 * 2
def baseEnd_778862 : Nat := 399930569522236932543085

theorem tailTrace_778862 : CollatzResearch.WordTrace tailWord_778862 prefixEnd_778862 399930569522236932543085 := by
  unfold tailWord_778862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3550928863040433485565355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18938287269548978589681893 3550928863040433485565355)
  ·
    refine ⟨5326393294560650228348033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3550928863040433485565355 5326393294560650228348033)
    ·
      refine ⟨3994794970920487671261025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5326393294560650228348033 3994794970920487671261025)
      ·
        refine ⟨2996096228190365753445769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3994794970920487671261025 2996096228190365753445769)
        ·
          refine ⟨2247072171142774315084327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2996096228190365753445769 2247072171142774315084327)
          ·
            refine ⟨3370608256714161472626491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247072171142774315084327 3370608256714161472626491)
            ·
              refine ⟨5055912385071242208939737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370608256714161472626491 5055912385071242208939737)
              ·
                refine ⟨3791934288803431656704803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5055912385071242208939737 3791934288803431656704803)
                ·
                  refine ⟨5687901433205147485057205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791934288803431656704803 5687901433205147485057205)
                  ·
                    refine ⟨533240759362982576724113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5687901433205147485057205 533240759362982576724113)
                    ·
                      refine ⟨399930569522236932543085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533240759362982576724113 399930569522236932543085)
                      ·
                        rfl

theorem cell23_778862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_778862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778862 prefixEnd_778862 := by exact prefixLift 778862
  have htrace : WordTrace (prefixWord ++ tailWord_778862) baseStart_778862 baseEnd_778862 := by
    simpa [prefixWord, tailWord_778862, baseEnd_778862] using wordTrace_append hprefix tailTrace_778862
  have hstable : (prefixWord ++ tailWord_778862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778862).length < 2 ^ (prefixWord ++ tailWord_778862).sum := by decide
  have hdescent : baseEnd_778862 < baseStart_778862 := by decide
  rcases family_descends (prefixWord ++ tailWord_778862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778885 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 4, 4]
def baseStart_778885 : Nat := 118140960795 + 778885 * 2 ^ 59
def prefixEnd_778885 : Nat := 4983230072969 + 3 ^ 40 * 778885 * 2
def baseEnd_778885 : Nat := 133314126525763447518493

theorem tailTrace_778885 : CollatzResearch.WordTrace tailWord_778885 prefixEnd_778885 133314126525763447518493 := by
  unfold tailWord_778885
  simp only [CollatzResearch.WordTrace]
  refine ⟨28408269783240142812610109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18938846522160095208406739 28408269783240142812610109)
  ·
    refine ⟨10653101168715053554728791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28408269783240142812610109 10653101168715053554728791)
    ·
      refine ⟨15979651753072580332093187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10653101168715053554728791 15979651753072580332093187)
      ·
        refine ⟨23969477629608870498139781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15979651753072580332093187 23969477629608870498139781)
        ·
          refine ⟨4494277055551663218401209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23969477629608870498139781 4494277055551663218401209)
          ·
            refine ⟨3370707791663747413800907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4494277055551663218401209 3370707791663747413800907)
            ·
              refine ⟨5056061687495621120701361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3370707791663747413800907 5056061687495621120701361)
              ·
                refine ⟨3792046265621715840526021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5056061687495621120701361 3792046265621715840526021)
                ·
                  refine ⟨711008674804071720098629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3792046265621715840526021 711008674804071720098629)
                  ·
                    refine ⟨133314126525763447518493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 711008674804071720098629 133314126525763447518493)
                    ·
                      rfl

theorem cell23_778885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_778885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778885 prefixEnd_778885 := by exact prefixLift 778885
  have htrace : WordTrace (prefixWord ++ tailWord_778885) baseStart_778885 baseEnd_778885 := by
    simpa [prefixWord, tailWord_778885, baseEnd_778885] using wordTrace_append hprefix tailTrace_778885
  have hstable : (prefixWord ++ tailWord_778885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778885).length < 2 ^ (prefixWord ++ tailWord_778885).sum := by decide
  have hdescent : baseEnd_778885 < baseStart_778885 := by decide
  rcases family_descends (prefixWord ++ tailWord_778885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778909 : List Nat := [1, 4, 2, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_778909 : Nat := 118140960795 + 778909 * 2 ^ 59
def prefixEnd_778909 : Nat := 4983230072969 + 3 ^ 40 * 778909 * 2
def baseEnd_778909 : Nat := 399954703112998248655369

theorem tailTrace_778909 : CollatzResearch.WordTrace tailWord_778909 prefixEnd_778909 399954703112998248655369 := by
  unfold tailWord_778909
  simp only [CollatzResearch.WordTrace]
  refine ⟨28409145135153194911483781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18939430090102129940989187 28409145135153194911483781)
  ·
    refine ⟨5326714712841224045903209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28409145135153194911483781 5326714712841224045903209)
    ·
      refine ⟨3995036034630918034427407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5326714712841224045903209 3995036034630918034427407)
      ·
        refine ⟨5992554051946377051641111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995036034630918034427407 5992554051946377051641111)
        ·
          refine ⟨8988831077919565577461667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5992554051946377051641111 8988831077919565577461667)
          ·
            refine ⟨13483246616879348366192501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8988831077919565577461667 13483246616879348366192501)
            ·
              refine ⟨1264054370332438909330547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13483246616879348366192501 1264054370332438909330547)
              ·
                refine ⟨1896081555498658363995821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264054370332438909330547 1896081555498658363995821)
                ·
                  refine ⟨711030583311996886498433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1896081555498658363995821 711030583311996886498433)
                  ·
                    refine ⟨533272937483997664873825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 711030583311996886498433 533272937483997664873825)
                    ·
                      refine ⟨399954703112998248655369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533272937483997664873825 399954703112998248655369)
                      ·
                        rfl

theorem cell23_778909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_778909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778909 prefixEnd_778909 := by exact prefixLift 778909
  have htrace : WordTrace (prefixWord ++ tailWord_778909) baseStart_778909 baseEnd_778909 := by
    simpa [prefixWord, tailWord_778909, baseEnd_778909] using wordTrace_append hprefix tailTrace_778909
  have hstable : (prefixWord ++ tailWord_778909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778909).length < 2 ^ (prefixWord ++ tailWord_778909).sum := by decide
  have hdescent : baseEnd_778909 < baseStart_778909 := by decide
  rcases family_descends (prefixWord ++ tailWord_778909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778926 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_778926 : Nat := 118140960795 + 778926 * 2 ^ 59
def prefixEnd_778926 : Nat := 4983230072969 + 3 ^ 40 * 778926 * 2
def baseEnd_778926 : Nat := 399963432284124682142791

theorem tailTrace_778926 : CollatzResearch.WordTrace tailWord_778926 prefixEnd_778926 399963432284124682142791 := by
  unfold tailWord_778926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551220647011450851856579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18939843450727737876568421 3551220647011450851856579)
  ·
    refine ⟨5326830970517176277784869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3551220647011450851856579 5326830970517176277784869)
    ·
      refine ⟨998780806971970552084663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5326830970517176277784869 998780806971970552084663)
      ·
        refine ⟨1498171210457955828126995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998780806971970552084663 1498171210457955828126995)
        ·
          refine ⟨2247256815686933742190493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498171210457955828126995 2247256815686933742190493)
          ·
            refine ⟨842721305882600153321435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2247256815686933742190493 842721305882600153321435)
            ·
              refine ⟨1264081958823900229982153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842721305882600153321435 1264081958823900229982153)
              ·
                refine ⟨948061469117925172486615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264081958823900229982153 948061469117925172486615)
                ·
                  refine ⟨1422092203676887758729923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948061469117925172486615 1422092203676887758729923)
                  ·
                    refine ⟨2133138305515331638094885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1422092203676887758729923 2133138305515331638094885)
                    ·
                      refine ⟨399963432284124682142791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2133138305515331638094885 399963432284124682142791)
                      ·
                        rfl

theorem cell23_778926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_778926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778926 prefixEnd_778926 := by exact prefixLift 778926
  have htrace : WordTrace (prefixWord ++ tailWord_778926) baseStart_778926 baseEnd_778926 := by
    simpa [prefixWord, tailWord_778926, baseEnd_778926] using wordTrace_append hprefix tailTrace_778926
  have hstable : (prefixWord ++ tailWord_778926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778926).length < 2 ^ (prefixWord ++ tailWord_778926).sum := by decide
  have hdescent : baseEnd_778926 < baseStart_778926 := by decide
  rcases family_descends (prefixWord ++ tailWord_778926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778929 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 3]
def baseStart_778929 : Nat := 118140960795 + 778929 * 2 ^ 59
def prefixEnd_778929 : Nat := 4983230072969 + 3 ^ 40 * 778929 * 2
def baseEnd_778929 : Nat := 399964972726088170405277

theorem tailTrace_778929 : CollatzResearch.WordTrace tailWord_778929 prefixEnd_778929 399964972726088170405277 := by
  unfold tailWord_778929
  simp only [CollatzResearch.WordTrace]
  refine ⟨28409874595080738327211841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18939916396720492218141227 28409874595080738327211841)
  ·
    refine ⟨21307405946310553745408881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28409874595080738327211841 21307405946310553745408881)
    ·
      refine ⟨15980554459732915309056661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21307405946310553745408881 15980554459732915309056661)
      ·
        refine ⟨749088490299980405112031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15980554459732915309056661 749088490299980405112031)
        ·
          refine ⟨1123632735449970607668047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749088490299980405112031 1123632735449970607668047)
          ·
            refine ⟨1685449103174955911502071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123632735449970607668047 1685449103174955911502071)
            ·
              refine ⟨2528173654762433867253107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685449103174955911502071 2528173654762433867253107)
              ·
                refine ⟨3792260482143650800879661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528173654762433867253107 3792260482143650800879661)
                ·
                  refine ⟨1422097680803869050329873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3792260482143650800879661 1422097680803869050329873)
                  ·
                    refine ⟨1066573260602901787747405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1422097680803869050329873 1066573260602901787747405)
                    ·
                      refine ⟨399964972726088170405277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1066573260602901787747405 399964972726088170405277)
                      ·
                        rfl

theorem cell23_778929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_778929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778929 prefixEnd_778929 := by exact prefixLift 778929
  have htrace : WordTrace (prefixWord ++ tailWord_778929) baseStart_778929 baseEnd_778929 := by
    simpa [prefixWord, tailWord_778929, baseEnd_778929] using wordTrace_append hprefix tailTrace_778929
  have hstable : (prefixWord ++ tailWord_778929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778929).length < 2 ^ (prefixWord ++ tailWord_778929).sum := by decide
  have hdescent : baseEnd_778929 < baseStart_778929 := by decide
  rcases family_descends (prefixWord ++ tailWord_778929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778942 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3]
def baseStart_778942 : Nat := 118140960795 + 778942 * 2 ^ 59
def prefixEnd_778942 : Nat := 4983230072969 + 3 ^ 40 * 778942 * 2
def baseEnd_778942 : Nat := 399971647974596619542717

theorem tailTrace_778942 : CollatzResearch.WordTrace tailWord_778942 prefixEnd_778942 399971647974596619542717 := by
  unfold tailWord_778942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3551293593004205193429385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18940232496022427698290053 3551293593004205193429385)
  ·
    refine ⟨2663470194753153895072039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3551293593004205193429385 2663470194753153895072039)
    ·
      refine ⟨3995205292129730842608059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663470194753153895072039 3995205292129730842608059)
      ·
        refine ⟨5992807938194596263912089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3995205292129730842608059 5992807938194596263912089)
        ·
          refine ⟨4494605953645947197934067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5992807938194596263912089 4494605953645947197934067)
          ·
            refine ⟨6741908930468920796901101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4494605953645947197934067 6741908930468920796901101)
            ·
              refine ⟨2528215848925845298837913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6741908930468920796901101 2528215848925845298837913)
              ·
                refine ⟨1896161886694383974128435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528215848925845298837913 1896161886694383974128435)
                ·
                  refine ⟨2844242830041575961192653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896161886694383974128435 2844242830041575961192653)
                  ·
                    refine ⟨1066591061265590985447245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2844242830041575961192653 1066591061265590985447245)
                    ·
                      refine ⟨399971647974596619542717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1066591061265590985447245 399971647974596619542717)
                      ·
                        rfl

theorem cell23_778942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_778942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778942 prefixEnd_778942 := by exact prefixLift 778942
  have htrace : WordTrace (prefixWord ++ tailWord_778942) baseStart_778942 baseEnd_778942 := by
    simpa [prefixWord, tailWord_778942, baseEnd_778942] using wordTrace_append hprefix tailTrace_778942
  have hstable : (prefixWord ++ tailWord_778942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778942).length < 2 ^ (prefixWord ++ tailWord_778942).sum := by decide
  have hdescent : baseEnd_778942 < baseStart_778942 := by decide
  rcases family_descends (prefixWord ++ tailWord_778942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778975 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 2, 6]
def baseStart_778975 : Nat := 118140960795 + 778975 * 2 ^ 59
def prefixEnd_778975 : Nat := 4983230072969 + 3 ^ 40 * 778975 * 2
def baseEnd_778975 : Nat := 133329530945398330143355

theorem tailTrace_778975 : CollatzResearch.WordTrace tailWord_778975 prefixEnd_778975 133329530945398330143355 := by
  unfold tailWord_778975
  simp only [CollatzResearch.WordTrace]
  refine ⟨28411552352914088183386379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18941034901942725455590919 28411552352914088183386379)
  ·
    refine ⟨42617328529371132275079569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28411552352914088183386379 42617328529371132275079569)
    ·
      refine ⟨31962996397028349206309677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42617328529371132275079569 31962996397028349206309677)
      ·
        refine ⟨11986123648885630952366129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31962996397028349206309677 11986123648885630952366129)
        ·
          refine ⟨8989592736664223214274597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11986123648885630952366129 8989592736664223214274597)
          ·
            refine ⟨1685548638124541852676487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8989592736664223214274597 1685548638124541852676487)
            ·
              refine ⟨2528322957186812779014731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685548638124541852676487 2528322957186812779014731)
              ·
                refine ⟨3792484435780219168522097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2528322957186812779014731 3792484435780219168522097)
                ·
                  refine ⟨2844363326835164376391573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3792484435780219168522097 2844363326835164376391573)
                  ·
                    refine ⟨133329530945398330143355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2844363326835164376391573 133329530945398330143355)
                    ·
                      rfl

theorem cell23_778975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_778975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778975 prefixEnd_778975 := by exact prefixLift 778975
  have htrace : WordTrace (prefixWord ++ tailWord_778975) baseStart_778975 baseEnd_778975 := by
    simpa [prefixWord, tailWord_778975, baseEnd_778975] using wordTrace_append hprefix tailTrace_778975
  have hstable : (prefixWord ++ tailWord_778975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778975).length < 2 ^ (prefixWord ++ tailWord_778975).sum := by decide
  have hdescent : baseEnd_778975 < baseStart_778975 := by decide
  rcases family_descends (prefixWord ++ tailWord_778975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_778997 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_778997 : Nat := 118140960795 + 778997 * 2 ^ 59
def prefixEnd_778997 : Nat := 4983230072969 + 3 ^ 40 * 778997 * 2
def baseEnd_778997 : Nat := 399999889410593904354965

theorem tailTrace_778997 : CollatzResearch.WordTrace tailWord_778997 prefixEnd_778997 399999889410593904354965 := by
  unfold tailWord_778997
  simp only [CollatzResearch.WordTrace]
  refine ⟨28412354758834385940687245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18941569839222923960458163 28412354758834385940687245)
  ·
    refine ⟨10654633034562894727757717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28412354758834385940687245 10654633034562894727757717)
    ·
      refine ⟨499435923495135690363643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10654633034562894727757717 499435923495135690363643)
      ·
        refine ⟨749153885242703535545465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499435923495135690363643 749153885242703535545465)
        ·
          refine ⟨561865413932027651659099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749153885242703535545465 561865413932027651659099)
          ·
            refine ⟨842798120898041477488649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561865413932027651659099 842798120898041477488649)
            ·
              refine ⟨632098590673531108116487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842798120898041477488649 632098590673531108116487)
              ·
                refine ⟨948147886010296662174731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632098590673531108116487 948147886010296662174731)
                ·
                  refine ⟨1422221829015444993262097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948147886010296662174731 1422221829015444993262097)
                  ·
                    refine ⟨1066666371761583744946573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1422221829015444993262097 1066666371761583744946573)
                    ·
                      refine ⟨399999889410593904354965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1066666371761583744946573 399999889410593904354965)
                      ·
                        rfl

theorem cell23_778997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_778997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_778997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_778997 prefixEnd_778997 := by exact prefixLift 778997
  have htrace : WordTrace (prefixWord ++ tailWord_778997) baseStart_778997 baseEnd_778997 := by
    simpa [prefixWord, tailWord_778997, baseEnd_778997] using wordTrace_append hprefix tailTrace_778997
  have hstable : (prefixWord ++ tailWord_778997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_778997).length < 2 ^ (prefixWord ++ tailWord_778997).sum := by decide
  have hdescent : baseEnd_778997 < baseStart_778997 := by decide
  rcases family_descends (prefixWord ++ tailWord_778997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779016 : List Nat := [2, 1, 3, 2, 2, 2, 3, 2, 2, 2, 2]
def baseStart_779016 : Nat := 118140960795 + 779016 * 2 ^ 59
def prefixEnd_779016 : Nat := 4983230072969 + 3 ^ 40 * 779016 * 2
def baseEnd_779016 : Nat := 400009645543029330017377

theorem tailTrace_779016 : CollatzResearch.WordTrace tailWord_779016 prefixEnd_779016 400009645543029330017377 := by
  unfold tailWord_779016
  simp only [CollatzResearch.WordTrace]
  refine ⟨14206523872882776092814451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18942031830510368123752601 14206523872882776092814451)
  ·
    refine ⟨21309785809324164139221677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14206523872882776092814451 21309785809324164139221677)
    ·
      refine ⟨7991169678496561552208129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21309785809324164139221677 7991169678496561552208129)
      ·
        refine ⟨5993377258872421164156097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7991169678496561552208129 5993377258872421164156097)
        ·
          refine ⟨4495032944154315873117073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5993377258872421164156097 4495032944154315873117073)
          ·
            refine ⟨3371274708115736904837805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495032944154315873117073 3371274708115736904837805)
            ·
              refine ⟨1264228015543401339314177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3371274708115736904837805 1264228015543401339314177)
              ·
                refine ⟨948171011657551004485633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264228015543401339314177 948171011657551004485633)
                ·
                  refine ⟨711128258743163253364225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 948171011657551004485633 711128258743163253364225)
                  ·
                    refine ⟨533346194057372440023169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 711128258743163253364225 533346194057372440023169)
                    ·
                      refine ⟨400009645543029330017377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533346194057372440023169 400009645543029330017377)
                      ·
                        rfl

theorem cell23_779016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_779016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779016 prefixEnd_779016 := by exact prefixLift 779016
  have htrace : WordTrace (prefixWord ++ tailWord_779016) baseStart_779016 baseEnd_779016 := by
    simpa [prefixWord, tailWord_779016, baseEnd_779016] using wordTrace_append hprefix tailTrace_779016
  have hstable : (prefixWord ++ tailWord_779016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779016).length < 2 ^ (prefixWord ++ tailWord_779016).sum := by decide
  have hdescent : baseEnd_779016 < baseStart_779016 := by decide
  rcases family_descends (prefixWord ++ tailWord_779016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779069 : List Nat := [1, 4, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_779069 : Nat := 118140960795 + 779069 * 2 ^ 59
def prefixEnd_779069 : Nat := 4983230072969 + 3 ^ 40 * 779069 * 2
def baseEnd_779069 : Nat := 133345620005905874218211

theorem tailTrace_779069 : CollatzResearch.WordTrace tailWord_779069 prefixEnd_779069 133345620005905874218211 := by
  unfold tailWord_779069
  simp only [CollatzResearch.WordTrace]
  refine ⟨28414980814573542237308261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18943320543049028158205507 28414980814573542237308261)
  ·
    refine ⟨5327808902732539169495299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28414980814573542237308261 5327808902732539169495299)
    ·
      refine ⟨7991713354098808754242949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5327808902732539169495299 7991713354098808754242949)
      ·
        refine ⟨1498446253893526641420553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7991713354098808754242949 1498446253893526641420553)
        ·
          refine ⟨1123834690420144981065415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1498446253893526641420553 1123834690420144981065415)
          ·
            refine ⟨1685752035630217471598123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123834690420144981065415 1685752035630217471598123)
            ·
              refine ⟨2528628053445326207397185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685752035630217471598123 2528628053445326207397185)
              ·
                refine ⟨1896471040083994655547889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528628053445326207397185 1896471040083994655547889)
                ·
                  refine ⟨1422353280062995991660917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896471040083994655547889 1422353280062995991660917)
                  ·
                    refine ⟨133345620005905874218211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1422353280062995991660917 133345620005905874218211)
                    ·
                      rfl

theorem cell23_779069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_779069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779069 prefixEnd_779069 := by exact prefixLift 779069
  have htrace : WordTrace (prefixWord ++ tailWord_779069) baseStart_779069 baseEnd_779069 := by
    simpa [prefixWord, tailWord_779069, baseEnd_779069] using wordTrace_append hprefix tailTrace_779069
  have hstable : (prefixWord ++ tailWord_779069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779069).length < 2 ^ (prefixWord ++ tailWord_779069).sum := by decide
  have hdescent : baseEnd_779069 < baseStart_779069 := by decide
  rcases family_descends (prefixWord ++ tailWord_779069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779072 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 4, 4, 2]
def baseStart_779072 : Nat := 118140960795 + 779072 * 2 ^ 59
def prefixEnd_779072 : Nat := 4983230072969 + 3 ^ 40 * 779072 * 2
def baseEnd_779072 : Nat := 400038400459681110917119

theorem tailTrace_779072 : CollatzResearch.WordTrace tailWord_779072 prefixEnd_779072 400038400459681110917119 := by
  unfold tailWord_779072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14207545116781336874833735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18943393489041782499778313 14207545116781336874833735)
  ·
    refine ⟨21311317675172005312250603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14207545116781336874833735 21311317675172005312250603)
    ·
      refine ⟨31966976512758007968375905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21311317675172005312250603 31966976512758007968375905)
      ·
        refine ⟨23975232384568505976281929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31966976512758007968375905 23975232384568505976281929)
        ·
          refine ⟨17981424288426379482211447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23975232384568505976281929 17981424288426379482211447)
          ·
            refine ⟨26972136432639569223317171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17981424288426379482211447 26972136432639569223317171)
            ·
              refine ⟨40458204648959353834975757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26972136432639569223317171 40458204648959353834975757)
              ·
                refine ⟨15171826743359757688115909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40458204648959353834975757 15171826743359757688115909)
                ·
                  refine ⟨2844717514379954566521733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15171826743359757688115909 2844717514379954566521733)
                  ·
                    refine ⟨533384533946241481222825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2844717514379954566521733 533384533946241481222825)
                    ·
                      refine ⟨400038400459681110917119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533384533946241481222825 400038400459681110917119)
                      ·
                        rfl

theorem cell23_779072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_779072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779072 prefixEnd_779072 := by exact prefixLift 779072
  have htrace : WordTrace (prefixWord ++ tailWord_779072) baseStart_779072 baseEnd_779072 := by
    simpa [prefixWord, tailWord_779072, baseEnd_779072] using wordTrace_append hprefix tailTrace_779072
  have hstable : (prefixWord ++ tailWord_779072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779072).length < 2 ^ (prefixWord ++ tailWord_779072).sum := by decide
  have hdescent : baseEnd_779072 < baseStart_779072 := by decide
  rcases family_descends (prefixWord ++ tailWord_779072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779073 : List Nat := [1, 2, 5, 3, 1, 1, 3, 2, 5]
def baseStart_779073 : Nat := 118140960795 + 779073 * 2 ^ 59
def prefixEnd_779073 : Nat := 4983230072969 + 3 ^ 40 * 779073 * 2
def baseEnd_779073 : Nat := 44448768215592845222735

theorem tailTrace_779073 : CollatzResearch.WordTrace tailWord_779073 prefixEnd_779073 44448768215592845222735 := by
  unfold tailWord_779073
  simp only [CollatzResearch.WordTrace]
  refine ⟨28415126706559050920453873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18943417804372700613635915 28415126706559050920453873)
  ·
    refine ⟨21311345029919288190340405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28415126706559050920453873 21311345029919288190340405)
    ·
      refine ⟨1997938596554933267844413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21311345029919288190340405 1997938596554933267844413)
      ·
        refine ⟨749226973708099975441655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1997938596554933267844413 749226973708099975441655)
        ·
          refine ⟨1123840460562149963162483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749226973708099975441655 1123840460562149963162483)
          ·
            refine ⟨1685760690843224944743725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123840460562149963162483 1685760690843224944743725)
            ·
              refine ⟨632160259066209354278897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1685760690843224944743725 632160259066209354278897)
              ·
                refine ⟨474120194299657015709173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632160259066209354278897 474120194299657015709173)
                ·
                  refine ⟨44448768215592845222735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 474120194299657015709173 44448768215592845222735)
                  ·
                    rfl

theorem cell23_779073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 2, 5].length) (baseStart_779073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779073 prefixEnd_779073 := by exact prefixLift 779073
  have htrace : WordTrace (prefixWord ++ tailWord_779073) baseStart_779073 baseEnd_779073 := by
    simpa [prefixWord, tailWord_779073, baseEnd_779073] using wordTrace_append hprefix tailTrace_779073
  have hstable : (prefixWord ++ tailWord_779073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779073).length < 2 ^ (prefixWord ++ tailWord_779073).sum := by decide
  have hdescent : baseEnd_779073 < baseStart_779073 := by decide
  rcases family_descends (prefixWord ++ tailWord_779073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779082 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 3, 4]
def baseStart_779082 : Nat := 118140960795 + 779082 * 2 ^ 59
def prefixEnd_779082 : Nat := 4983230072969 + 3 ^ 40 * 779082 * 2
def baseEnd_779082 : Nat := 133347845088742023930691

theorem tailTrace_779082 : CollatzResearch.WordTrace tailWord_779082 prefixEnd_779082 133347845088742023930691 := by
  unfold tailWord_779082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103863740881611364382875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18943636642350963638354333 7103863740881611364382875)
  ·
    refine ⟨10655795611322417046574313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7103863740881611364382875 10655795611322417046574313)
    ·
      refine ⟨7991846708491812784930735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10655795611322417046574313 7991846708491812784930735)
      ·
        refine ⟨11987770062737719177396103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7991846708491812784930735 11987770062737719177396103)
        ·
          refine ⟨17981655094106578766094155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11987770062737719177396103 17981655094106578766094155)
          ·
            refine ⟨26972482641159868149141233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17981655094106578766094155 26972482641159868149141233)
            ·
              refine ⟨20229361980869901111855925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26972482641159868149141233 20229361980869901111855925)
              ·
                refine ⟨1896502685706553229236493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20229361980869901111855925 1896502685706553229236493)
                ·
                  refine ⟨711188507139957460963685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1896502685706553229236493 711188507139957460963685)
                  ·
                    refine ⟨133347845088742023930691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 711188507139957460963685 133347845088742023930691)
                    ·
                      rfl

theorem cell23_779082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_779082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779082 prefixEnd_779082 := by exact prefixLift 779082
  have htrace : WordTrace (prefixWord ++ tailWord_779082) baseStart_779082 baseEnd_779082 := by
    simpa [prefixWord, tailWord_779082, baseEnd_779082] using wordTrace_append hprefix tailTrace_779082
  have hstable : (prefixWord ++ tailWord_779082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779082).length < 2 ^ (prefixWord ++ tailWord_779082).sum := by decide
  have hdescent : baseEnd_779082 < baseStart_779082 := by decide
  rcases family_descends (prefixWord ++ tailWord_779082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779106 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_779106 : Nat := 118140960795 + 779106 * 2 ^ 59
def prefixEnd_779106 : Nat := 4983230072969 + 3 ^ 40 * 779106 * 2
def baseEnd_779106 : Nat := 400055858801933977891963

theorem tailTrace_779106 : CollatzResearch.WordTrace tailWord_779106 prefixEnd_779106 400055858801933977891963 := by
  unfold tailWord_779106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7104082578859874389101293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18944220210292998370936781 7104082578859874389101293)
  ·
    refine ⟨2664030967072452895912985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7104082578859874389101293 2664030967072452895912985)
    ·
      refine ⟨1998023225304339671934739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2664030967072452895912985 1998023225304339671934739)
      ·
        refine ⟨2997034837956509507902109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998023225304339671934739 2997034837956509507902109)
        ·
          refine ⟨1123888064233691065463291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2997034837956509507902109 1123888064233691065463291)
          ·
            refine ⟨1685832096350536598194937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123888064233691065463291 1685832096350536598194937)
            ·
              refine ⟨1264374072262902448646203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1685832096350536598194937 1264374072262902448646203)
              ·
                refine ⟨1896561108394353672969305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264374072262902448646203 1896561108394353672969305)
                ·
                  refine ⟨1422420831295765254726979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896561108394353672969305 1422420831295765254726979)
                  ·
                    refine ⟨2133631246943647882090469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1422420831295765254726979 2133631246943647882090469)
                    ·
                      refine ⟨400055858801933977891963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2133631246943647882090469 400055858801933977891963)
                      ·
                        rfl

theorem cell23_779106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_779106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779106 prefixEnd_779106 := by exact prefixLift 779106
  have htrace : WordTrace (prefixWord ++ tailWord_779106) baseStart_779106 baseEnd_779106 := by
    simpa [prefixWord, tailWord_779106, baseEnd_779106] using wordTrace_append hprefix tailTrace_779106
  have hstable : (prefixWord ++ tailWord_779106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779106).length < 2 ^ (prefixWord ++ tailWord_779106).sum := by decide
  have hdescent : baseEnd_779106 < baseStart_779106 := by decide
  rcases family_descends (prefixWord ++ tailWord_779106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779126 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3]
def baseStart_779126 : Nat := 118140960795 + 779126 * 2 ^ 59
def prefixEnd_779126 : Nat := 4983230072969 + 3 ^ 40 * 779126 * 2
def baseEnd_779126 : Nat := 400066128415023899641871

theorem tailTrace_779126 : CollatzResearch.WordTrace tailWord_779126 prefixEnd_779126 400066128415023899641871 := by
  unfold tailWord_779126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776066235960440060758327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18944706516911360648088821 1776066235960440060758327)
  ·
    refine ⟨2664099353940660091137491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1776066235960440060758327 2664099353940660091137491)
    ·
      refine ⟨3996149030910990136706237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2664099353940660091137491 3996149030910990136706237)
      ·
        refine ⟨1498555886591621301264839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3996149030910990136706237 1498555886591621301264839)
        ·
          refine ⟨2247833829887431951897259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498555886591621301264839 2247833829887431951897259)
          ·
            refine ⟨3371750744831147927845889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2247833829887431951897259 3371750744831147927845889)
            ·
              refine ⟨2528813058623360945884417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3371750744831147927845889 2528813058623360945884417)
              ·
                refine ⟨1896609793967520709413313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528813058623360945884417 1896609793967520709413313)
                ·
                  refine ⟨1422457345475640532059985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1896609793967520709413313 1422457345475640532059985)
                  ·
                    refine ⟨1066843009106730399044989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1422457345475640532059985 1066843009106730399044989)
                    ·
                      refine ⟨400066128415023899641871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1066843009106730399044989 400066128415023899641871)
                      ·
                        rfl

theorem cell23_779126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_779126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779126 prefixEnd_779126 := by exact prefixLift 779126
  have htrace : WordTrace (prefixWord ++ tailWord_779126) baseStart_779126 baseEnd_779126 := by
    simpa [prefixWord, tailWord_779126, baseEnd_779126] using wordTrace_append hprefix tailTrace_779126
  have hstable : (prefixWord ++ tailWord_779126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779126).length < 2 ^ (prefixWord ++ tailWord_779126).sum := by decide
  have hdescent : baseEnd_779126 < baseStart_779126 := by decide
  rcases family_descends (prefixWord ++ tailWord_779126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779139 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 3]
def baseStart_779139 : Nat := 118140960795 + 779139 * 2 ^ 59
def prefixEnd_779139 : Nat := 4983230072969 + 3 ^ 40 * 779139 * 2
def baseEnd_779139 : Nat := 400072803663532348779311

theorem tailTrace_779139 : CollatzResearch.WordTrace tailWord_779139 prefixEnd_779139 400072803663532348779311 := by
  unfold tailWord_779139
  simp only [CollatzResearch.WordTrace]
  refine ⟨28417533924319944192356471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18945022616213296128237647 28417533924319944192356471)
  ·
    refine ⟨42626300886479916288534707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28417533924319944192356471 42626300886479916288534707)
    ·
      refine ⟨63939451329719874432802061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42626300886479916288534707 63939451329719874432802061)
      ·
        refine ⟨23977294248644952912300773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63939451329719874432802061 23977294248644952912300773)
        ·
          refine ⟨4495742671620928671056395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23977294248644952912300773 4495742671620928671056395)
          ·
            refine ⟨6743614007431393006584593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495742671620928671056395 6743614007431393006584593)
            ·
              refine ⟨5057710505573544754938445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6743614007431393006584593 5057710505573544754938445)
              ·
                refine ⟨1896641439590079283101917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5057710505573544754938445 1896641439590079283101917)
                ·
                  refine ⟨711240539846279731163219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1896641439590079283101917 711240539846279731163219)
                  ·
                    refine ⟨1066860809769419596744829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 711240539846279731163219 1066860809769419596744829)
                    ·
                      refine ⟨400072803663532348779311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1066860809769419596744829 400072803663532348779311)
                      ·
                        rfl

theorem cell23_779139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_779139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779139 prefixEnd_779139 := by exact prefixLift 779139
  have htrace : WordTrace (prefixWord ++ tailWord_779139) baseStart_779139 baseEnd_779139 := by
    simpa [prefixWord, tailWord_779139, baseEnd_779139] using wordTrace_append hprefix tailTrace_779139
  have hstable : (prefixWord ++ tailWord_779139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779139).length < 2 ^ (prefixWord ++ tailWord_779139).sum := by decide
  have hdescent : baseEnd_779139 < baseStart_779139 := by decide
  rcases family_descends (prefixWord ++ tailWord_779139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779156 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_779156 : Nat := 118140960795 + 779156 * 2 ^ 59
def prefixEnd_779156 : Nat := 4983230072969 + 3 ^ 40 * 779156 * 2
def baseEnd_779156 : Nat := 400081532834658782266733

theorem tailTrace_779156 : CollatzResearch.WordTrace tailWord_779156 prefixEnd_779156 400081532834658782266733 := by
  unfold tailWord_779156
  simp only [CollatzResearch.WordTrace]
  refine ⟨14209076982629178047862661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18945435976838904063816881 14209076982629178047862661)
  ·
    refine ⟨2664201934242970883974249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14209076982629178047862661 2664201934242970883974249)
    ·
      refine ⟨1998151450682228162980687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2664201934242970883974249 1998151450682228162980687)
      ·
        refine ⟨2997227176023342244471031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998151450682228162980687 2997227176023342244471031)
        ·
          refine ⟨4495840764035013366706547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997227176023342244471031 4495840764035013366706547)
          ·
            refine ⟨6743761146052520050059821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495840764035013366706547 6743761146052520050059821)
            ·
              refine ⟨2528910429769695018772433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6743761146052520050059821 2528910429769695018772433)
              ·
                refine ⟨1896682822327271264079325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2528910429769695018772433 1896682822327271264079325)
                ·
                  refine ⟨711256058372726724029747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1896682822327271264079325 711256058372726724029747)
                  ·
                    refine ⟨1066884087559090086044621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 711256058372726724029747 1066884087559090086044621)
                    ·
                      refine ⟨400081532834658782266733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1066884087559090086044621 400081532834658782266733)
                      ·
                        rfl

theorem cell23_779156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_779156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779156 prefixEnd_779156 := by exact prefixLift 779156
  have htrace : WordTrace (prefixWord ++ tailWord_779156) baseStart_779156 baseEnd_779156 := by
    simpa [prefixWord, tailWord_779156, baseEnd_779156] using wordTrace_append hprefix tailTrace_779156
  have hstable : (prefixWord ++ tailWord_779156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779156).length < 2 ^ (prefixWord ++ tailWord_779156).sum := by decide
  have hdescent : baseEnd_779156 < baseStart_779156 := by decide
  rcases family_descends (prefixWord ++ tailWord_779156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779172 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_779172 : Nat := 118140960795 + 779172 * 2 ^ 59
def prefixEnd_779172 : Nat := 4983230072969 + 3 ^ 40 * 779172 * 2
def baseEnd_779172 : Nat := 133363249508376906555553

theorem tailTrace_779172 : CollatzResearch.WordTrace tailWord_779172 prefixEnd_779172 133363249508376906555553 := by
  unfold tailWord_779172
  simp only [CollatzResearch.WordTrace]
  refine ⟨14209368766600195414153885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18945825022133593885538513 14209368766600195414153885)
  ·
    refine ⟨5328513287475073280307707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14209368766600195414153885 5328513287475073280307707)
    ·
      refine ⟨7992769931212609920461561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5328513287475073280307707 7992769931212609920461561)
      ·
        refine ⟨5994577448409457440346171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7992769931212609920461561 5994577448409457440346171)
        ·
          refine ⟨8991866172614186160519257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5994577448409457440346171 8991866172614186160519257)
          ·
            refine ⟨6743899629460639620389443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8991866172614186160519257 6743899629460639620389443)
            ·
              refine ⟨10115849444190959430584165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6743899629460639620389443 10115849444190959430584165)
              ·
                refine ⟨1896721770785804893234531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10115849444190959430584165 1896721770785804893234531)
                ·
                  refine ⟨2845082656178707339851797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1896721770785804893234531 2845082656178707339851797)
                  ·
                    refine ⟨133363249508376906555553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2845082656178707339851797 133363249508376906555553)
                    ·
                      rfl

theorem cell23_779172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_779172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779172 prefixEnd_779172 := by exact prefixLift 779172
  have htrace : WordTrace (prefixWord ++ tailWord_779172) baseStart_779172 baseEnd_779172 := by
    simpa [prefixWord, tailWord_779172, baseEnd_779172] using wordTrace_append hprefix tailTrace_779172
  have hstable : (prefixWord ++ tailWord_779172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779172).length < 2 ^ (prefixWord ++ tailWord_779172).sum := by decide
  have hdescent : baseEnd_779172 < baseStart_779172 := by decide
  rcases family_descends (prefixWord ++ tailWord_779172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779189 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 4, 4]
def baseStart_779189 : Nat := 118140960795 + 779189 * 2 ^ 59
def prefixEnd_779189 : Nat := 4983230072969 + 3 ^ 40 * 779189 * 2
def baseEnd_779189 : Nat := 133366159232085717718027

theorem tailTrace_779189 : CollatzResearch.WordTrace tailWord_779189 prefixEnd_779189 133366159232085717718027 := by
  unfold tailWord_779189
  simp only [CollatzResearch.WordTrace]
  refine ⟨28419357574138802731676621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18946238382759201821117747 28419357574138802731676621)
  ·
    refine ⟨10657259090302051024378733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28419357574138802731676621 10657259090302051024378733)
    ·
      refine ⟨3996472158863269134142025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10657259090302051024378733 3996472158863269134142025)
      ·
        refine ⟨2997354119147451850606519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3996472158863269134142025 2997354119147451850606519)
        ·
          refine ⟨4496031178721177775909779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2997354119147451850606519 4496031178721177775909779)
          ·
            refine ⟨6744046768081766663864669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4496031178721177775909779 6744046768081766663864669)
            ·
              refine ⟨2529017538030662498949251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6744046768081766663864669 2529017538030662498949251)
              ·
                refine ⟨3793526307045993748423877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529017538030662498949251 3793526307045993748423877)
                ·
                  refine ⟨711286182571123827829477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3793526307045993748423877 711286182571123827829477)
                  ·
                    refine ⟨133366159232085717718027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 711286182571123827829477 133366159232085717718027)
                    ·
                      rfl

theorem cell23_779189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_779189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779189 prefixEnd_779189 := by exact prefixLift 779189
  have htrace : WordTrace (prefixWord ++ tailWord_779189) baseStart_779189 baseEnd_779189 := by
    simpa [prefixWord, tailWord_779189, baseEnd_779189] using wordTrace_append hprefix tailTrace_779189
  have hstable : (prefixWord ++ tailWord_779189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779189).length < 2 ^ (prefixWord ++ tailWord_779189).sum := by decide
  have hdescent : baseEnd_779189 < baseStart_779189 := by decide
  rcases family_descends (prefixWord ++ tailWord_779189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779316 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_779316 : Nat := 118140960795 + 779316 * 2 ^ 59
def prefixEnd_779316 : Nat := 4983230072969 + 3 ^ 40 * 779316 * 2
def baseEnd_779316 : Nat := 400163689739378156265997

theorem tailTrace_779316 : CollatzResearch.WordTrace tailWord_779316 prefixEnd_779316 400163689739378156265997 := by
  unfold tailWord_779316
  simp only [CollatzResearch.WordTrace]
  refine ⟨14211994822339351710774901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18949326429785802281033201 14211994822339351710774901)
  ·
    refine ⟨1332374514594314222885147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14211994822339351710774901 1332374514594314222885147)
    ·
      refine ⟨1998561771891471334327721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1332374514594314222885147 1998561771891471334327721)
      ·
        refine ⟨1498921328918603500745791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1998561771891471334327721 1498921328918603500745791)
        ·
          refine ⟨2248381993377905251118687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498921328918603500745791 2248381993377905251118687)
          ·
            refine ⟨3372572990066857876678031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2248381993377905251118687 3372572990066857876678031)
            ·
              refine ⟨5058859485100286815017047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3372572990066857876678031 5058859485100286815017047)
              ·
                refine ⟨7588289227650430222525571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5058859485100286815017047 7588289227650430222525571)
                ·
                  refine ⟨11382433841475645333788357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7588289227650430222525571 11382433841475645333788357)
                  ·
                    refine ⟨2134206345276683500085317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11382433841475645333788357 2134206345276683500085317)
                    ·
                      refine ⟨400163689739378156265997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2134206345276683500085317 400163689739378156265997)
                      ·
                        rfl

theorem cell23_779316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_779316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779316 prefixEnd_779316 := by exact prefixLift 779316
  have htrace : WordTrace (prefixWord ++ tailWord_779316) baseStart_779316 baseEnd_779316 := by
    simpa [prefixWord, tailWord_779316, baseEnd_779316] using wordTrace_append hprefix tailTrace_779316
  have hstable : (prefixWord ++ tailWord_779316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779316).length < 2 ^ (prefixWord ++ tailWord_779316).sum := by decide
  have hdescent : baseEnd_779316 < baseStart_779316 := by decide
  rcases family_descends (prefixWord ++ tailWord_779316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779326 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_779326 : Nat := 118140960795 + 779326 * 2 ^ 59
def prefixEnd_779326 : Nat := 4983230072969 + 3 ^ 40 * 779326 * 2
def baseEnd_779326 : Nat := 44463202727324790793439

theorem tailTrace_779326 : CollatzResearch.WordTrace tailWord_779326 prefixEnd_779326 44463202727324790793439 := by
  unfold tailWord_779326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553044296830309391176729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18949569583094983419609221 3553044296830309391176729)
  ·
    refine ⟨2664783222622732043382547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3553044296830309391176729 2664783222622732043382547)
    ·
      refine ⟨3997174833934098065073821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2664783222622732043382547 3997174833934098065073821)
      ·
        refine ⟨1498940562725286774402683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3997174833934098065073821 1498940562725286774402683)
        ·
          refine ⟨2248410844087930161604025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498940562725286774402683 2248410844087930161604025)
          ·
            refine ⟨1686308133065947621203019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2248410844087930161604025 1686308133065947621203019)
            ·
              refine ⟨2529462199598921431804529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686308133065947621203019 2529462199598921431804529)
              ·
                refine ⟨1897096649699191073853397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529462199598921431804529 1897096649699191073853397)
                ·
                  refine ⟨44463202727324790793439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1897096649699191073853397 44463202727324790793439)
                  ·
                    rfl

theorem cell23_779326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_779326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779326 prefixEnd_779326 := by exact prefixLift 779326
  have htrace : WordTrace (prefixWord ++ tailWord_779326) baseStart_779326 baseEnd_779326 := by
    simpa [prefixWord, tailWord_779326, baseEnd_779326] using wordTrace_append hprefix tailTrace_779326
  have hstable : (prefixWord ++ tailWord_779326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779326).length < 2 ^ (prefixWord ++ tailWord_779326).sum := by decide
  have hdescent : baseEnd_779326 < baseStart_779326 := by decide
  rcases family_descends (prefixWord ++ tailWord_779326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779359 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_779359 : Nat := 118140960795 + 779359 * 2 ^ 59
def prefixEnd_779359 : Nat := 4983230072969 + 3 ^ 40 * 779359 * 2
def baseEnd_779359 : Nat := 400185769407521488028299

theorem tailTrace_779359 : CollatzResearch.WordTrace tailWord_779359 prefixEnd_779359 400185769407521488028299 := by
  unfold tailWord_779359
  simp only [CollatzResearch.WordTrace]
  refine ⟨28425557983522921765365131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18950371989015281176910087 28425557983522921765365131)
  ·
    refine ⟨42638336975284382648047697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28425557983522921765365131 42638336975284382648047697)
    ·
      refine ⟨31978752731463286986035773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42638336975284382648047697 31978752731463286986035773)
      ·
        refine ⟨11992032274298732619763415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31978752731463286986035773 11992032274298732619763415)
        ·
          refine ⟨17988048411448098929645123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11992032274298732619763415 17988048411448098929645123)
          ·
            refine ⟨26982072617172148394467685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17988048411448098929645123 26982072617172148394467685)
            ·
              refine ⟨5059138615719777823962691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26982072617172148394467685 5059138615719777823962691)
              ·
                refine ⟨7588707923579666735944037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5059138615719777823962691 7588707923579666735944037)
                ·
                  refine ⟨1422882735671187512989507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7588707923579666735944037 1422882735671187512989507)
                  ·
                    refine ⟨2134324103506781269484261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1422882735671187512989507 2134324103506781269484261)
                    ·
                      refine ⟨400185769407521488028299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2134324103506781269484261 400185769407521488028299)
                      ·
                        rfl

theorem cell23_779359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_779359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779359 prefixEnd_779359 := by exact prefixLift 779359
  have htrace : WordTrace (prefixWord ++ tailWord_779359) baseStart_779359 baseEnd_779359 := by
    simpa [prefixWord, tailWord_779359, baseEnd_779359] using wordTrace_append hprefix tailTrace_779359
  have hstable : (prefixWord ++ tailWord_779359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779359).length < 2 ^ (prefixWord ++ tailWord_779359).sum := by decide
  have hdescent : baseEnd_779359 < baseStart_779359 := by decide
  rcases family_descends (prefixWord ++ tailWord_779359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779376 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 2, 4, 2]
def baseStart_779376 : Nat := 118140960795 + 779376 * 2 ^ 59
def prefixEnd_779376 : Nat := 4983230072969 + 3 ^ 40 * 779376 * 2
def baseEnd_779376 : Nat := 400194498578647921515721

theorem tailTrace_779376 : CollatzResearch.WordTrace tailWord_779376 prefixEnd_779376 400194498578647921515721 := by
  unfold tailWord_779376
  simp only [CollatzResearch.WordTrace]
  refine ⟨14213089012230666834366991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18950785349640889112489321 14213089012230666834366991)
  ·
    refine ⟨21319633518346000251550487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14213089012230666834366991 21319633518346000251550487)
    ·
      refine ⟨31979450277519000377325731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21319633518346000251550487 31979450277519000377325731)
      ·
        refine ⟨47969175416278500565988597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31979450277519000377325731 47969175416278500565988597)
        ·
          refine ⟨4497110195276109428061431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47969175416278500565988597 4497110195276109428061431)
          ·
            refine ⟨6745665292914164142092147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497110195276109428061431 6745665292914164142092147)
            ·
              refine ⟨10118497939371246213138221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6745665292914164142092147 10118497939371246213138221)
              ·
                refine ⟨3794436727264217329926833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10118497939371246213138221 3794436727264217329926833)
                ·
                  refine ⟨2845827545448162997445125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3794436727264217329926833 2845827545448162997445125)
                  ·
                    refine ⟨533592664771530562020961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2845827545448162997445125 533592664771530562020961)
                    ·
                      refine ⟨400194498578647921515721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533592664771530562020961 400194498578647921515721)
                      ·
                        rfl

theorem cell23_779376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 4, 2].length) (baseStart_779376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779376 prefixEnd_779376 := by exact prefixLift 779376
  have htrace : WordTrace (prefixWord ++ tailWord_779376) baseStart_779376 baseEnd_779376 := by
    simpa [prefixWord, tailWord_779376, baseEnd_779376] using wordTrace_append hprefix tailTrace_779376
  have hstable : (prefixWord ++ tailWord_779376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779376).length < 2 ^ (prefixWord ++ tailWord_779376).sum := by decide
  have hdescent : baseEnd_779376 < baseStart_779376 := by decide
  rcases family_descends (prefixWord ++ tailWord_779376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779389 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_779389 : Nat := 118140960795 + 779389 * 2 ^ 59
def prefixEnd_779389 : Nat := 4983230072969 + 3 ^ 40 * 779389 * 2
def baseEnd_779389 : Nat := 400201173827156370653161

theorem tailTrace_779389 : CollatzResearch.WordTrace tailWord_779389 prefixEnd_779389 400201173827156370653161 := by
  unfold tailWord_779389
  simp only [CollatzResearch.WordTrace]
  refine ⟨28426652173414236888957221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18951101448942824592638147 28426652173414236888957221)
  ·
    refine ⟨5329997282515169416679479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28426652173414236888957221 5329997282515169416679479)
    ·
      refine ⟨7994995923772754125019219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329997282515169416679479 7994995923772754125019219)
      ·
        refine ⟨11992493885659131187528829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7994995923772754125019219 11992493885659131187528829)
        ·
          refine ⟨4497185207122174195323311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11992493885659131187528829 4497185207122174195323311)
          ·
            refine ⟨6745777810683261292984967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4497185207122174195323311 6745777810683261292984967)
            ·
              refine ⟨10118666716024891939477451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6745777810683261292984967 10118666716024891939477451)
              ·
                refine ⟨15178000074037337909216177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10118666716024891939477451 15178000074037337909216177)
                ·
                  refine ⟨11383500055528003431912133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15178000074037337909216177 11383500055528003431912133)
                  ·
                    refine ⟨2134406260411500643483525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11383500055528003431912133 2134406260411500643483525)
                    ·
                      refine ⟨400201173827156370653161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2134406260411500643483525 400201173827156370653161)
                      ·
                        rfl

theorem cell23_779389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_779389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779389 prefixEnd_779389 := by exact prefixLift 779389
  have htrace : WordTrace (prefixWord ++ tailWord_779389) baseStart_779389 baseEnd_779389 := by
    simpa [prefixWord, tailWord_779389, baseEnd_779389] using wordTrace_append hprefix tailTrace_779389
  have hstable : (prefixWord ++ tailWord_779389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779389).length < 2 ^ (prefixWord ++ tailWord_779389).sum := by decide
  have hdescent : baseEnd_779389 < baseStart_779389 := by decide
  rcases family_descends (prefixWord ++ tailWord_779389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779396 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_779396 : Nat := 118140960795 + 779396 * 2 ^ 59
def prefixEnd_779396 : Nat := 4983230072969 + 3 ^ 40 * 779396 * 2
def baseEnd_779396 : Nat := 400204768191737843265629

theorem tailTrace_779396 : CollatzResearch.WordTrace tailWord_779396 prefixEnd_779396 400204768191737843265629 := by
  unfold tailWord_779396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14213453742194438542231021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18951271656259251389641361 14213453742194438542231021)
  ·
    refine ⟨5330045153322914453336633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14213453742194438542231021 5330045153322914453336633)
    ·
      refine ⟨3997533864992185840002475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5330045153322914453336633 3997533864992185840002475)
      ·
        refine ⟨5996300797488278760003713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997533864992185840002475 5996300797488278760003713)
        ·
          refine ⟨4497225598116209070002785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5996300797488278760003713 4497225598116209070002785)
          ·
            refine ⟨3372919198587156802502089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4497225598116209070002785 3372919198587156802502089)
            ·
              refine ⟨2529689398940367601876567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3372919198587156802502089 2529689398940367601876567)
              ·
                refine ⟨3794534098410551402814851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2529689398940367601876567 3794534098410551402814851)
                ·
                  refine ⟨5691801147615827104222277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794534098410551402814851 5691801147615827104222277)
                  ·
                    refine ⟨1067212715177967582041677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5691801147615827104222277 1067212715177967582041677)
                    ·
                      refine ⟨400204768191737843265629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1067212715177967582041677 400204768191737843265629)
                      ·
                        rfl

theorem cell23_779396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_779396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779396 prefixEnd_779396 := by exact prefixLift 779396
  have htrace : WordTrace (prefixWord ++ tailWord_779396) baseStart_779396 baseEnd_779396 := by
    simpa [prefixWord, tailWord_779396, baseEnd_779396] using wordTrace_append hprefix tailTrace_779396
  have hstable : (prefixWord ++ tailWord_779396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779396).length < 2 ^ (prefixWord ++ tailWord_779396).sum := by decide
  have hdescent : baseEnd_779396 < baseStart_779396 := by decide
  rcases family_descends (prefixWord ++ tailWord_779396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779436 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 1, 5, 2]
def baseStart_779436 : Nat := 118140960795 + 779436 * 2 ^ 59
def prefixEnd_779436 : Nat := 4983230072969 + 3 ^ 40 * 779436 * 2
def baseEnd_779436 : Nat := 400225307417917686765445

theorem tailTrace_779436 : CollatzResearch.WordTrace tailWord_779436 prefixEnd_779436 400225307417917686765445 := by
  unfold tailWord_779436
  simp only [CollatzResearch.WordTrace]
  refine ⟨14214183202121981957959081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18952244269495975943945441 14214183202121981957959081)
  ·
    refine ⟨10660637401591486468469311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14214183202121981957959081 10660637401591486468469311)
    ·
      refine ⟨15990956102387229702703967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10660637401591486468469311 15990956102387229702703967)
      ·
        refine ⟨23986434153580844554055951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15990956102387229702703967 23986434153580844554055951)
        ·
          refine ⟨35979651230371266831083927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23986434153580844554055951 35979651230371266831083927)
          ·
            refine ⟨53969476845556900246625891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35979651230371266831083927 53969476845556900246625891)
            ·
              refine ⟨80954215268335350369938837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53969476845556900246625891 80954215268335350369938837)
              ·
                refine ⟨3794728840703219548590883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80954215268335350369938837 3794728840703219548590883)
                ·
                  refine ⟨5692093261054829322886325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3794728840703219548590883 5692093261054829322886325)
                  ·
                    refine ⟨533633743223890249020593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5692093261054829322886325 533633743223890249020593)
                    ·
                      refine ⟨400225307417917686765445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533633743223890249020593 400225307417917686765445)
                      ·
                        rfl

theorem cell23_779436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_779436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779436 prefixEnd_779436 := by exact prefixLift 779436
  have htrace : WordTrace (prefixWord ++ tailWord_779436) baseStart_779436 baseEnd_779436 := by
    simpa [prefixWord, tailWord_779436, baseEnd_779436] using wordTrace_append hprefix tailTrace_779436
  have hstable : (prefixWord ++ tailWord_779436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779436).length < 2 ^ (prefixWord ++ tailWord_779436).sum := by decide
  have hdescent : baseEnd_779436 < baseStart_779436 := by decide
  rcases family_descends (prefixWord ++ tailWord_779436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779453 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_779453 : Nat := 118140960795 + 779453 * 2 ^ 59
def prefixEnd_779453 : Nat := 4983230072969 + 3 ^ 40 * 779453 * 2
def baseEnd_779453 : Nat := 400234036589044120252867

theorem tailTrace_779453 : CollatzResearch.WordTrace tailWord_779453 prefixEnd_779453 400234036589044120252867 := by
  unfold tailWord_779453
  simp only [CollatzResearch.WordTrace]
  refine ⟨28428986445182375819287013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18952657630121583879524675 28428986445182375819287013)
  ·
    refine ⟨5330434958471695466116315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28428986445182375819287013 5330434958471695466116315)
    ·
      refine ⟨7995652437707543199174473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5330434958471695466116315 7995652437707543199174473)
      ·
        refine ⟨5996739328280657399380855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7995652437707543199174473 5996739328280657399380855)
        ·
          refine ⟨8995108992420986099071283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5996739328280657399380855 8995108992420986099071283)
          ·
            refine ⟨13492663488631479148606925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8995108992420986099071283 13492663488631479148606925)
            ·
              refine ⟨5059748808236804680727597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13492663488631479148606925 5059748808236804680727597)
              ·
                refine ⟨1897405803088801755272849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5059748808236804680727597 1897405803088801755272849)
                ·
                  refine ⟨1423054352316601316454637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1897405803088801755272849 1423054352316601316454637)
                  ·
                    refine ⟨533645382118725493670489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1423054352316601316454637 533645382118725493670489)
                    ·
                      refine ⟨400234036589044120252867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533645382118725493670489 400234036589044120252867)
                      ·
                        rfl

theorem cell23_779453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_779453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779453 prefixEnd_779453 := by exact prefixLift 779453
  have htrace : WordTrace (prefixWord ++ tailWord_779453) baseStart_779453 baseEnd_779453 := by
    simpa [prefixWord, tailWord_779453, baseEnd_779453] using wordTrace_append hprefix tailTrace_779453
  have hstable : (prefixWord ++ tailWord_779453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779453).length < 2 ^ (prefixWord ++ tailWord_779453).sum := by decide
  have hdescent : baseEnd_779453 < baseStart_779453 := by decide
  rcases family_descends (prefixWord ++ tailWord_779453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779477 : List Nat := [1, 3, 2, 4, 1, 2, 1, 4, 1, 1, 3]
def baseStart_779477 : Nat := 118140960795 + 779477 * 2 ^ 59
def prefixEnd_779477 : Nat := 4983230072969 + 3 ^ 40 * 779477 * 2
def baseEnd_779477 : Nat := 400246360124752026352757

theorem tailTrace_779477 : CollatzResearch.WordTrace tailWord_779477 prefixEnd_779477 400246360124752026352757 := by
  unfold tailWord_779477
  simp only [CollatzResearch.WordTrace]
  refine ⟨28429861797095427918160685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18953241198063618612107123 28429861797095427918160685)
  ·
    refine ⟨10661198173910785469310257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28429861797095427918160685 10661198173910785469310257)
    ·
      refine ⟨7995898630433089101982693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10661198173910785469310257 7995898630433089101982693)
      ·
        refine ⟨1499230993206204206621755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7995898630433089101982693 1499230993206204206621755)
        ·
          refine ⟨2248846489809306309932633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499230993206204206621755 2248846489809306309932633)
          ·
            refine ⟨1686634867356979732449475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2248846489809306309932633 1686634867356979732449475)
            ·
              refine ⟨2529952301035469598674213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686634867356979732449475 2529952301035469598674213)
              ·
                refine ⟨474366056444150549751415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2529952301035469598674213 474366056444150549751415)
                ·
                  refine ⟨711549084666225824627123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474366056444150549751415 711549084666225824627123)
                  ·
                    refine ⟨1067323626999338736940685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 711549084666225824627123 1067323626999338736940685)
                    ·
                      refine ⟨400246360124752026352757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1067323626999338736940685 400246360124752026352757)
                      ·
                        rfl

theorem cell23_779477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_779477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779477 prefixEnd_779477 := by exact prefixLift 779477
  have htrace : WordTrace (prefixWord ++ tailWord_779477) baseStart_779477 baseEnd_779477 := by
    simpa [prefixWord, tailWord_779477, baseEnd_779477] using wordTrace_append hprefix tailTrace_779477
  have hstable : (prefixWord ++ tailWord_779477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779477).length < 2 ^ (prefixWord ++ tailWord_779477).sum := by decide
  have hdescent : baseEnd_779477 < baseStart_779477 := by decide
  rcases family_descends (prefixWord ++ tailWord_779477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779479 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_779479 : Nat := 118140960795 + 779479 * 2 ^ 59
def prefixEnd_779479 : Nat := 4983230072969 + 3 ^ 40 * 779479 * 2
def baseEnd_779479 : Nat := 400247387086061018527747

theorem tailTrace_779479 : CollatzResearch.WordTrace tailWord_779479 prefixEnd_779479 400247387086061018527747 := by
  unfold tailWord_779479
  simp only [CollatzResearch.WordTrace]
  refine ⟨28429934743088182259733491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18953289828725454839822327 28429934743088182259733491)
  ·
    refine ⟨42644902114632273389600237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28429934743088182259733491 42644902114632273389600237)
    ·
      refine ⟨15991838292987102521100089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42644902114632273389600237 15991838292987102521100089)
      ·
        refine ⟨11993878719740326890825067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15991838292987102521100089 11993878719740326890825067)
        ·
          refine ⟨17990818079610490336237601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11993878719740326890825067 17990818079610490336237601)
          ·
            refine ⟨13493113559707867752178201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17990818079610490336237601 13493113559707867752178201)
            ·
              refine ⟨10119835169780900814133651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13493113559707867752178201 10119835169780900814133651)
              ·
                refine ⟨15179752754671351221200477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10119835169780900814133651 15179752754671351221200477)
                ·
                  refine ⟨5692407283001756707950179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15179752754671351221200477 5692407283001756707950179)
                  ·
                    refine ⟨8538610924502635061925269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5692407283001756707950179 8538610924502635061925269)
                    ·
                      refine ⟨400247387086061018527747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8538610924502635061925269 400247387086061018527747)
                      ·
                        rfl

theorem cell23_779479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_779479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779479 prefixEnd_779479 := by exact prefixLift 779479
  have htrace : WordTrace (prefixWord ++ tailWord_779479) baseStart_779479 baseEnd_779479 := by
    simpa [prefixWord, tailWord_779479, baseEnd_779479] using wordTrace_append hprefix tailTrace_779479
  have hstable : (prefixWord ++ tailWord_779479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779479).length < 2 ^ (prefixWord ++ tailWord_779479).sum := by decide
  have hdescent : baseEnd_779479 < baseStart_779479 := by decide
  rcases family_descends (prefixWord ++ tailWord_779479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779493 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 1, 6]
def baseStart_779493 : Nat := 118140960795 + 779493 * 2 ^ 59
def prefixEnd_779493 : Nat := 4983230072969 + 3 ^ 40 * 779493 * 2
def baseEnd_779493 : Nat := 133418191938407987917561

theorem tailTrace_779493 : CollatzResearch.WordTrace tailWord_779493 prefixEnd_779493 133418191938407987917561 := by
  unfold tailWord_779493
  simp only [CollatzResearch.WordTrace]
  refine ⟨28430445365037462650743133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18953630243358308433828755 28430445365037462650743133)
  ·
    refine ⟨10661417011889048494028675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28430445365037462650743133 10661417011889048494028675)
    ·
      refine ⟨15992125517833572741043013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10661417011889048494028675 15992125517833572741043013)
      ·
        refine ⟨2998523534593794888945565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15992125517833572741043013 2998523534593794888945565)
        ·
          refine ⟨1124446325472673083354587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2998523534593794888945565 1124446325472673083354587)
          ·
            refine ⟨1686669488209009625031881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124446325472673083354587 1686669488209009625031881)
            ·
              refine ⟨1265002116156757218773911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1686669488209009625031881 1265002116156757218773911)
              ·
                refine ⟨1897503174235135828160867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265002116156757218773911 1897503174235135828160867)
                ·
                  refine ⟨2846254761352703742241301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1897503174235135828160867 2846254761352703742241301)
                  ·
                    refine ⟨133418191938407987917561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2846254761352703742241301 133418191938407987917561)
                    ·
                      rfl

theorem cell23_779493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_779493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779493 prefixEnd_779493 := by exact prefixLift 779493
  have htrace : WordTrace (prefixWord ++ tailWord_779493) baseStart_779493 baseEnd_779493 := by
    simpa [prefixWord, tailWord_779493, baseEnd_779493] using wordTrace_append hprefix tailTrace_779493
  have hstable : (prefixWord ++ tailWord_779493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779493).length < 2 ^ (prefixWord ++ tailWord_779493).sum := by decide
  have hdescent : baseEnd_779493 < baseStart_779493 := by decide
  rcases family_descends (prefixWord ++ tailWord_779493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779500 : List Nat := [2, 2, 1, 1, 2, 5, 1, 2, 3, 2, 2]
def baseStart_779500 : Nat := 118140960795 + 779500 * 2 ^ 59
def prefixEnd_779500 : Nat := 4983230072969 + 3 ^ 40 * 779500 * 2
def baseEnd_779500 : Nat := 400258170179805436365151

theorem tailTrace_779500 : CollatzResearch.WordTrace tailWord_779500 prefixEnd_779500 400258170179805436365151 := by
  unfold tailWord_779500
  simp only [CollatzResearch.WordTrace]
  refine ⟨14215350338006051423123977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18953800450674735230831969 14215350338006051423123977)
  ·
    refine ⟨10661512753504538567342983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14215350338006051423123977 10661512753504538567342983)
    ·
      refine ⟨15992269130256807851014475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10661512753504538567342983 15992269130256807851014475)
      ·
        refine ⟨23988403695385211776521713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15992269130256807851014475 23988403695385211776521713)
        ·
          refine ⟨17991302771538908832391285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23988403695385211776521713 17991302771538908832391285)
          ·
            refine ⟨1686684634831772703036683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17991302771538908832391285 1686684634831772703036683)
            ·
              refine ⟨2530026952247659054555025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686684634831772703036683 2530026952247659054555025)
              ·
                refine ⟨1897520214185744290916269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2530026952247659054555025 1897520214185744290916269)
                ·
                  refine ⟨711570080319654109093601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1897520214185744290916269 711570080319654109093601)
                  ·
                    refine ⟨533677560239740581820201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 711570080319654109093601 533677560239740581820201)
                    ·
                      refine ⟨400258170179805436365151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533677560239740581820201 400258170179805436365151)
                      ·
                        rfl

theorem cell23_779500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_779500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779500 prefixEnd_779500 := by exact prefixLift 779500
  have htrace : WordTrace (prefixWord ++ tailWord_779500) baseStart_779500 baseEnd_779500 := by
    simpa [prefixWord, tailWord_779500, baseEnd_779500] using wordTrace_append hprefix tailTrace_779500
  have hstable : (prefixWord ++ tailWord_779500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779500).length < 2 ^ (prefixWord ++ tailWord_779500).sum := by decide
  have hdescent : baseEnd_779500 < baseStart_779500 := by decide
  rcases family_descends (prefixWord ++ tailWord_779500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779576 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_779576 : Nat := 118140960795 + 779576 * 2 ^ 59
def prefixEnd_779576 : Nat := 4983230072969 + 3 ^ 40 * 779576 * 2
def baseEnd_779576 : Nat := 400297194709547139014801

theorem tailTrace_779576 : CollatzResearch.WordTrace tailWord_779576 prefixEnd_779576 400297194709547139014801 := by
  unfold tailWord_779576
  simp only [CollatzResearch.WordTrace]
  refine ⟨14216736311868383913007291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18955648415824511884009721 14216736311868383913007291)
  ·
    refine ⟨21325104467802575869510937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14216736311868383913007291 21325104467802575869510937)
    ·
      refine ⟨15993828350851931902133203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21325104467802575869510937 15993828350851931902133203)
      ·
        refine ⟨23990742526277897853199805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15993828350851931902133203 23990742526277897853199805)
        ·
          refine ⟨8996528447354211694949927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23990742526277897853199805 8996528447354211694949927)
          ·
            refine ⟨13494792671031317542424891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8996528447354211694949927 13494792671031317542424891)
            ·
              refine ⟨20242189006546976313637337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13494792671031317542424891 20242189006546976313637337)
              ·
                refine ⟨15181641754910232235228003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20242189006546976313637337 15181641754910232235228003)
                ·
                  refine ⟨22772462632365348352842005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15181641754910232235228003 22772462632365348352842005)
                  ·
                    refine ⟨1067459185892125704039469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22772462632365348352842005 1067459185892125704039469)
                    ·
                      refine ⟨400297194709547139014801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1067459185892125704039469 400297194709547139014801)
                      ·
                        rfl

theorem cell23_779576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_779576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779576 prefixEnd_779576 := by exact prefixLift 779576
  have htrace : WordTrace (prefixWord ++ tailWord_779576) baseStart_779576 baseEnd_779576 := by
    simpa [prefixWord, tailWord_779576, baseEnd_779576] using wordTrace_append hprefix tailTrace_779576
  have hstable : (prefixWord ++ tailWord_779576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779576).length < 2 ^ (prefixWord ++ tailWord_779576).sum := by decide
  have hdescent : baseEnd_779576 < baseStart_779576 := by decide
  rcases family_descends (prefixWord ++ tailWord_779576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779607 : List Nat := [1, 1, 3, 2, 3, 3, 1, 3, 2, 2, 2]
def baseStart_779607 : Nat := 118140960795 + 779607 * 2 ^ 59
def prefixEnd_779607 : Nat := 4983230072969 + 3 ^ 40 * 779607 * 2
def baseEnd_779607 : Nat := 400313112609836517727159

theorem tailTrace_779607 : CollatzResearch.WordTrace tailWord_779607 prefixEnd_779607 400313112609836517727159 := by
  unfold tailWord_779607
  simp only [CollatzResearch.WordTrace]
  refine ⟨28434603286624460120393075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18956402191082973413595383 28434603286624460120393075)
  ·
    refine ⟨42651904929936690180589613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28434603286624460120393075 42651904929936690180589613)
    ·
      refine ⟨15994464348726258817721105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42651904929936690180589613 15994464348726258817721105)
      ·
        refine ⟨11995848261544694113290829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15994464348726258817721105 11995848261544694113290829)
        ·
          refine ⟨4498443098079260292484061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11995848261544694113290829 4498443098079260292484061)
          ·
            refine ⟨1686916161779722609681523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4498443098079260292484061 1686916161779722609681523)
            ·
              refine ⟨2530374242669583914522285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686916161779722609681523 2530374242669583914522285)
              ·
                refine ⟨948890341001093967945857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2530374242669583914522285 948890341001093967945857)
                ·
                  refine ⟨711667755750820475959393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 948890341001093967945857 711667755750820475959393)
                  ·
                    refine ⟨533750816813115356969545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 711667755750820475959393 533750816813115356969545)
                    ·
                      refine ⟨400313112609836517727159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 533750816813115356969545 400313112609836517727159)
                      ·
                        rfl

theorem cell23_779607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_779607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779607 prefixEnd_779607 := by exact prefixLift 779607
  have htrace : WordTrace (prefixWord ++ tailWord_779607) baseStart_779607 baseEnd_779607 := by
    simpa [prefixWord, tailWord_779607, baseEnd_779607] using wordTrace_append hprefix tailTrace_779607
  have hstable : (prefixWord ++ tailWord_779607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779607).length < 2 ^ (prefixWord ++ tailWord_779607).sum := by decide
  have hdescent : baseEnd_779607 < baseStart_779607 := by decide
  rcases family_descends (prefixWord ++ tailWord_779607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779673 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 5, 4]
def baseStart_779673 : Nat := 118140960795 + 779673 * 2 ^ 59
def prefixEnd_779673 : Nat := 4983230072969 + 3 ^ 40 * 779673 * 2
def baseEnd_779673 : Nat := 133449000777677753167285

theorem tailTrace_779673 : CollatzResearch.WordTrace tailWord_779673 prefixEnd_779673 133449000777677753167285 := by
  unfold tailWord_779673
  simp only [CollatzResearch.WordTrace]
  refine ⟨28437010504385353392295673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18958007002923568928197115 28437010504385353392295673)
  ·
    refine ⟨21327757878289015044221755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28437010504385353392295673 21327757878289015044221755)
    ·
      refine ⟨31991636817433522566332633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21327757878289015044221755 31991636817433522566332633)
      ·
        refine ⟨23993727613075141924749475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31991636817433522566332633 23993727613075141924749475)
        ·
          refine ⟨35990591419612712887124213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23993727613075141924749475 35990591419612712887124213)
          ·
            refine ⟨3374117945588691833167895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35990591419612712887124213 3374117945588691833167895)
            ·
              refine ⟨5061176918383037749751843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3374117945588691833167895 5061176918383037749751843)
              ·
                refine ⟨7591765377574556624627765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5061176918383037749751843 7591765377574556624627765)
                ·
                  refine ⟨711728004147614683558853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7591765377574556624627765 711728004147614683558853)
                  ·
                    refine ⟨133449000777677753167285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 711728004147614683558853 133449000777677753167285)
                    ·
                      rfl

theorem cell23_779673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 5, 4].length) (baseStart_779673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779673 prefixEnd_779673 := by exact prefixLift 779673
  have htrace : WordTrace (prefixWord ++ tailWord_779673) baseStart_779673 baseEnd_779673 := by
    simpa [prefixWord, tailWord_779673, baseEnd_779673] using wordTrace_append hprefix tailTrace_779673
  have hstable : (prefixWord ++ tailWord_779673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779673).length < 2 ^ (prefixWord ++ tailWord_779673).sum := by decide
  have hdescent : baseEnd_779673 < baseStart_779673 := by decide
  rcases family_descends (prefixWord ++ tailWord_779673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779683 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 3]
def baseStart_779683 : Nat := 118140960795 + 779683 * 2 ^ 59
def prefixEnd_779683 : Nat := 4983230072969 + 3 ^ 40 * 779683 * 2
def baseEnd_779683 : Nat := 400352137139578220376809

theorem tailTrace_779683 : CollatzResearch.WordTrace tailWord_779683 prefixEnd_779683 400352137139578220376809 := by
  unfold tailWord_779683
  simp only [CollatzResearch.WordTrace]
  refine ⟨28437375234349125100159703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18958250156232750066773135 28437375234349125100159703)
  ·
    refine ⟨42656062851523687650239555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28437375234349125100159703 42656062851523687650239555)
    ·
      refine ⟨63984094277285531475359333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42656062851523687650239555 63984094277285531475359333)
      ·
        refine ⟨11997017676991037151629875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63984094277285531475359333 11997017676991037151629875)
        ·
          refine ⟨17995526515486555727444813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11997017676991037151629875 17995526515486555727444813)
          ·
            refine ⟨6748322443307458397791805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17995526515486555727444813 6748322443307458397791805)
            ·
              refine ⟨2530620916240296899171927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6748322443307458397791805 2530620916240296899171927)
              ·
                refine ⟨3795931374360445348757891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2530620916240296899171927 3795931374360445348757891)
                ·
                  refine ⟨5693897061540668023136837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3795931374360445348757891 5693897061540668023136837)
                  ·
                    refine ⟨1067605699038875254338157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5693897061540668023136837 1067605699038875254338157)
                    ·
                      refine ⟨400352137139578220376809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1067605699038875254338157 400352137139578220376809)
                      ·
                        rfl

theorem cell23_779683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_779683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779683 prefixEnd_779683 := by exact prefixLift 779683
  have htrace : WordTrace (prefixWord ++ tailWord_779683) baseStart_779683 baseEnd_779683 := by
    simpa [prefixWord, tailWord_779683, baseEnd_779683] using wordTrace_append hprefix tailTrace_779683
  have hstable : (prefixWord ++ tailWord_779683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779683).length < 2 ^ (prefixWord ++ tailWord_779683).sum := by decide
  have hdescent : baseEnd_779683 < baseStart_779683 := by decide
  rcases family_descends (prefixWord ++ tailWord_779683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779720 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 6]
def baseStart_779720 : Nat := 118140960795 + 779720 * 2 ^ 59
def prefixEnd_779720 : Nat := 4983230072969 + 3 ^ 40 * 779720 * 2
def baseEnd_779720 : Nat := 44485681769310508401571

theorem tailTrace_779720 : CollatzResearch.WordTrace tailWord_779720 prefixEnd_779720 44485681769310508401571 := by
  unfold tailWord_779720
  simp only [CollatzResearch.WordTrace]
  refine ⟨14219362367607540209628307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18959149823476720279504409 14219362367607540209628307)
  ·
    refine ⟨21329043551411310314442461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14219362367607540209628307 21329043551411310314442461)
    ·
      refine ⟨7998391331779241367915923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21329043551411310314442461 7998391331779241367915923)
      ·
        refine ⟨11997586997668862051873885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7998391331779241367915923 11997586997668862051873885)
        ·
          refine ⟨4499095124125823269452707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11997586997668862051873885 4499095124125823269452707)
          ·
            refine ⟨6748642686188734904179061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4499095124125823269452707 6748642686188734904179061)
            ·
              refine ⟨632685251830193897266787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6748642686188734904179061 632685251830193897266787)
              ·
                refine ⟨949027877745290845900181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632685251830193897266787 949027877745290845900181)
                ·
                  refine ⟨44485681769310508401571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 949027877745290845900181 44485681769310508401571)
                  ·
                    rfl

theorem cell23_779720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 6].length) (baseStart_779720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779720 prefixEnd_779720 := by exact prefixLift 779720
  have htrace : WordTrace (prefixWord ++ tailWord_779720) baseStart_779720 baseEnd_779720 := by
    simpa [prefixWord, tailWord_779720, baseEnd_779720] using wordTrace_append hprefix tailTrace_779720
  have hstable : (prefixWord ++ tailWord_779720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779720).length < 2 ^ (prefixWord ++ tailWord_779720).sum := by decide
  have hdescent : baseEnd_779720 < baseStart_779720 := by decide
  rcases family_descends (prefixWord ++ tailWord_779720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779903 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_779903 : Nat := 118140960795 + 779903 * 2 ^ 59
def prefixEnd_779903 : Nat := 4983230072969 + 3 ^ 40 * 779903 * 2
def baseEnd_779903 : Nat := 400465102883567359625797

theorem tailTrace_779903 : CollatzResearch.WordTrace tailWord_779903 prefixEnd_779903 400465102883567359625797 := by
  unfold tailWord_779903
  simp only [CollatzResearch.WordTrace]
  refine ⟨28445399293552102673168363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18963599529034735115445575 28445399293552102673168363)
  ·
    refine ⟨42668098940328154009752545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28445399293552102673168363 42668098940328154009752545)
    ·
      refine ⟨32001074205246115507314409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42668098940328154009752545 32001074205246115507314409)
      ·
        refine ⟨24000805653934586630485807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32001074205246115507314409 24000805653934586630485807)
        ·
          refine ⟨36001208480901879945728711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24000805653934586630485807 36001208480901879945728711)
          ·
            refine ⟨54001812721352819918593067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36001208480901879945728711 54001812721352819918593067)
            ·
              refine ⟨81002719082029229877889601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54001812721352819918593067 81002719082029229877889601)
              ·
                refine ⟨60752039311521922408417201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81002719082029229877889601 60752039311521922408417201)
                ·
                  refine ⟨45564029483641441806312901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60752039311521922408417201 45564029483641441806312901)
                  ·
                    refine ⟨8543255528182770338683669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45564029483641441806312901 8543255528182770338683669)
                    ·
                      refine ⟨400465102883567359625797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8543255528182770338683669 400465102883567359625797)
                      ·
                        rfl

theorem cell23_779903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_779903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779903 prefixEnd_779903 := by exact prefixLift 779903
  have htrace : WordTrace (prefixWord ++ tailWord_779903) baseStart_779903 baseEnd_779903 := by
    simpa [prefixWord, tailWord_779903, baseEnd_779903] using wordTrace_append hprefix tailTrace_779903
  have hstable : (prefixWord ++ tailWord_779903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779903).length < 2 ^ (prefixWord ++ tailWord_779903).sum := by decide
  have hdescent : baseEnd_779903 < baseStart_779903 := by decide
  rcases family_descends (prefixWord ++ tailWord_779903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779934 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 7]
def baseStart_779934 : Nat := 118140960795 + 779934 * 2 ^ 59
def prefixEnd_779934 : Nat := 4983230072969 + 3 ^ 40 * 779934 * 2
def baseEnd_779934 : Nat := 44497891198206304259795

theorem tailTrace_779934 : CollatzResearch.WordTrace tailWord_779934 prefixEnd_779934 44497891198206304259795 := by
  unfold tailWord_779934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555816244554974370943357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18964353304293196645031237 3555816244554974370943357)
  ·
    refine ⟨1333431091708115389103759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3555816244554974370943357 1333431091708115389103759)
    ·
      refine ⟨2000146637562173083655639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1333431091708115389103759 2000146637562173083655639)
      ·
        refine ⟨3000219956343259625483459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000146637562173083655639 3000219956343259625483459)
        ·
          refine ⟨4500329934514889438225189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3000219956343259625483459 4500329934514889438225189)
          ·
            refine ⟨843811862721541769667223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4500329934514889438225189 843811862721541769667223)
            ·
              refine ⟨1265717794082312654500835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843811862721541769667223 1265717794082312654500835)
              ·
                refine ⟨1898576691123468981751253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265717794082312654500835 1898576691123468981751253)
                ·
                  refine ⟨44497891198206304259795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1898576691123468981751253 44497891198206304259795)
                  ·
                    rfl

theorem cell23_779934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_779934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779934 prefixEnd_779934 := by exact prefixLift 779934
  have htrace : WordTrace (prefixWord ++ tailWord_779934) baseStart_779934 baseEnd_779934 := by
    simpa [prefixWord, tailWord_779934, baseEnd_779934] using wordTrace_append hprefix tailTrace_779934
  have hstable : (prefixWord ++ tailWord_779934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779934).length < 2 ^ (prefixWord ++ tailWord_779934).sum := by decide
  have hdescent : baseEnd_779934 < baseStart_779934 := by decide
  rcases family_descends (prefixWord ++ tailWord_779934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779940 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_779940 : Nat := 118140960795 + 779940 * 2 ^ 59
def prefixEnd_779940 : Nat := 4983230072969 + 3 ^ 40 * 779940 * 2
def baseEnd_779940 : Nat := 400484101667783714863127

theorem tailTrace_779940 : CollatzResearch.WordTrace tailWord_779940 prefixEnd_779940 400484101667783714863127 := by
  unfold tailWord_779940
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223374397209028996132637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18964499196278705328176849 14223374397209028996132637)
  ·
    refine ⟨5333765398953385873549739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14223374397209028996132637 5333765398953385873549739)
    ·
      refine ⟨8000648098430078810324609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5333765398953385873549739 8000648098430078810324609)
      ·
        refine ⟨6000486073822559107743457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8000648098430078810324609 6000486073822559107743457)
        ·
          refine ⟨4500364555366919330807593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6000486073822559107743457 4500364555366919330807593)
          ·
            refine ⟨3375273416525189498105695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4500364555366919330807593 3375273416525189498105695)
            ·
              refine ⟨5062910124787784247158543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375273416525189498105695 5062910124787784247158543)
              ·
                refine ⟨7594365187181676370737815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5062910124787784247158543 7594365187181676370737815)
                ·
                  refine ⟨11391547780772514556106723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7594365187181676370737815 11391547780772514556106723)
                  ·
                    refine ⟨17087321671158771834160085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11391547780772514556106723 17087321671158771834160085)
                    ·
                      refine ⟨400484101667783714863127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17087321671158771834160085 400484101667783714863127)
                      ·
                        rfl

theorem cell23_779940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_779940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779940 prefixEnd_779940 := by exact prefixLift 779940
  have htrace : WordTrace (prefixWord ++ tailWord_779940) baseStart_779940 baseEnd_779940 := by
    simpa [prefixWord, tailWord_779940, baseEnd_779940] using wordTrace_append hprefix tailTrace_779940
  have hstable : (prefixWord ++ tailWord_779940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779940).length < 2 ^ (prefixWord ++ tailWord_779940).sum := by decide
  have hdescent : baseEnd_779940 < baseStart_779940 := by decide
  rcases family_descends (prefixWord ++ tailWord_779940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_779967 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 4]
def baseStart_779967 : Nat := 118140960795 + 779967 * 2 ^ 59
def prefixEnd_779967 : Nat := 4983230072969 + 3 ^ 40 * 779967 * 2
def baseEnd_779967 : Nat := 400497965645455109225503

theorem tailTrace_779967 : CollatzResearch.WordTrace tailWord_779967 prefixEnd_779967 400497965645455109225503 := by
  unfold tailWord_779967
  simp only [CollatzResearch.WordTrace]
  refine ⟨28447733565320241603498155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18965155710213494402332103 28447733565320241603498155)
  ·
    refine ⟨42671600347980362405247233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28447733565320241603498155 42671600347980362405247233)
    ·
      refine ⟨32003700260985271803935425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42671600347980362405247233 32003700260985271803935425)
      ·
        refine ⟨24002775195738953852951569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32003700260985271803935425 24002775195738953852951569)
        ·
          refine ⟨18002081396804215389713677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24002775195738953852951569 18002081396804215389713677)
          ·
            refine ⟨6750780523801580771142629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18002081396804215389713677 6750780523801580771142629)
            ·
              refine ⟨1265771348212796394589243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6750780523801580771142629 1265771348212796394589243)
              ·
                refine ⟨1898657022319194591883865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265771348212796394589243 1898657022319194591883865)
                ·
                  refine ⟨1423992766739395943912899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1898657022319194591883865 1423992766739395943912899)
                  ·
                    refine ⟨2135989150109093915869349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1423992766739395943912899 2135989150109093915869349)
                    ·
                      refine ⟨400497965645455109225503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2135989150109093915869349 400497965645455109225503)
                      ·
                        rfl

theorem cell23_779967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_779967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_779967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_779967 prefixEnd_779967 := by exact prefixLift 779967
  have htrace : WordTrace (prefixWord ++ tailWord_779967) baseStart_779967 baseEnd_779967 := by
    simpa [prefixWord, tailWord_779967, baseEnd_779967] using wordTrace_append hprefix tailTrace_779967
  have hstable : (prefixWord ++ tailWord_779967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_779967).length < 2 ^ (prefixWord ++ tailWord_779967).sum := by decide
  have hdescent : baseEnd_779967 < baseStart_779967 := by decide
  rcases family_descends (prefixWord ++ tailWord_779967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780044 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 2, 3, 2]
def baseStart_780044 : Nat := 118140960795 + 780044 * 2 ^ 59
def prefixEnd_780044 : Nat := 4983230072969 + 3 ^ 40 * 780044 * 2
def baseEnd_780044 : Nat := 400537503655851307962649

theorem tailTrace_780044 : CollatzResearch.WordTrace tailWord_780044 prefixEnd_780044 400537503655851307962649 := by
  unfold tailWord_780044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14225270993020641877025593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18967027990694189169367457 14225270993020641877025593)
  ·
    refine ⟨10668953244765481407769195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14225270993020641877025593 10668953244765481407769195)
    ·
      refine ⟨16003429867148222111653793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10668953244765481407769195 16003429867148222111653793)
      ·
        refine ⟨12002572400361166583740345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16003429867148222111653793 12002572400361166583740345)
        ·
          refine ⟨9001929300270874937805259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12002572400361166583740345 9001929300270874937805259)
          ·
            refine ⟨13502893950406312406707889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9001929300270874937805259 13502893950406312406707889)
            ·
              refine ⟨10127170462804734305030917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13502893950406312406707889 10127170462804734305030917)
              ·
                refine ⟨1898844461775887682193297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10127170462804734305030917 1898844461775887682193297)
                ·
                  refine ⟨1424133346331915761644973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1898844461775887682193297 1424133346331915761644973)
                  ·
                    refine ⟨534050004874468410616865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424133346331915761644973 534050004874468410616865)
                    ·
                      refine ⟨400537503655851307962649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 534050004874468410616865 400537503655851307962649)
                      ·
                        rfl

theorem cell23_780044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_780044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780044 prefixEnd_780044 := by exact prefixLift 780044
  have htrace : WordTrace (prefixWord ++ tailWord_780044) baseStart_780044 baseEnd_780044 := by
    simpa [prefixWord, tailWord_780044, baseEnd_780044] using wordTrace_append hprefix tailTrace_780044
  have hstable : (prefixWord ++ tailWord_780044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780044).length < 2 ^ (prefixWord ++ tailWord_780044).sum := by decide
  have hdescent : baseEnd_780044 < baseStart_780044 := by decide
  rcases family_descends (prefixWord ++ tailWord_780044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780067 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 1, 6]
def baseStart_780067 : Nat := 118140960795 + 780067 * 2 ^ 59
def prefixEnd_780067 : Nat := 4983230072969 + 3 ^ 40 * 780067 * 2
def baseEnd_780067 : Nat := 133516437903634905991681

theorem tailTrace_780067 : CollatzResearch.WordTrace tailWord_780067 prefixEnd_780067 133516437903634905991681 := by
  unfold tailWord_780067
  simp only [CollatzResearch.WordTrace]
  refine ⟨28451380864957958682138455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18967587243305305788092303 28451380864957958682138455)
  ·
    refine ⟨42677071297436938023207683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28451380864957958682138455 42677071297436938023207683)
    ·
      refine ⟨64015606946155407034811525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42677071297436938023207683 64015606946155407034811525)
      ·
        refine ⟨12002926302404138819027161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64015606946155407034811525 12002926302404138819027161)
        ·
          refine ⟨9002194726803104114270371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12002926302404138819027161 9002194726803104114270371)
          ·
            refine ⟨13503292090204656171405557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9002194726803104114270371 13503292090204656171405557)
            ·
              refine ⟨1265933633456686516069271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13503292090204656171405557 1265933633456686516069271)
              ·
                refine ⟨1898900450185029774103907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1265933633456686516069271 1898900450185029774103907)
                ·
                  refine ⟨2848350675277544661155861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898900450185029774103907 2848350675277544661155861)
                  ·
                    refine ⟨133516437903634905991681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2848350675277544661155861 133516437903634905991681)
                    ·
                      rfl

theorem cell23_780067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 6].length) (baseStart_780067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780067 prefixEnd_780067 := by exact prefixLift 780067
  have htrace : WordTrace (prefixWord ++ tailWord_780067) baseStart_780067 baseEnd_780067 := by
    simpa [prefixWord, tailWord_780067, baseEnd_780067] using wordTrace_append hprefix tailTrace_780067
  have hstable : (prefixWord ++ tailWord_780067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780067).length < 2 ^ (prefixWord ++ tailWord_780067).sum := by decide
  have hdescent : baseEnd_780067 < baseStart_780067 := by decide
  rcases family_descends (prefixWord ++ tailWord_780067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780085 : List Nat := [1, 3, 3, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_780085 : Nat := 118140960795 + 780085 * 2 ^ 59
def prefixEnd_780085 : Nat := 4983230072969 + 3 ^ 40 * 780085 * 2
def baseEnd_780085 : Nat := 400558556362685647549961

theorem tailTrace_780085 : CollatzResearch.WordTrace tailWord_780085 prefixEnd_780085 400558556362685647549961 := by
  unfold tailWord_780085
  simp only [CollatzResearch.WordTrace]
  refine ⟨28452037378892747756293709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18968024919261831837529139 28452037378892747756293709)
  ·
    refine ⟨10669514017084780408610141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28452037378892747756293709 10669514017084780408610141)
    ·
      refine ⟨4001067756406792653228803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10669514017084780408610141 4001067756406792653228803)
      ·
        refine ⟨6001601634610188979843205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001067756406792653228803 6001601634610188979843205)
        ·
          refine ⟨1125300306489410433720601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6001601634610188979843205 1125300306489410433720601)
          ·
            refine ⟨843975229867057825290451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125300306489410433720601 843975229867057825290451)
            ·
              refine ⟨1265962844800586737935677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843975229867057825290451 1265962844800586737935677)
              ·
                refine ⟨474736066800220026725879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1265962844800586737935677 474736066800220026725879)
                ·
                  refine ⟨712104100200330040088819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474736066800220026725879 712104100200330040088819)
                  ·
                    refine ⟨1068156150300495060133229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 712104100200330040088819 1068156150300495060133229)
                    ·
                      refine ⟨400558556362685647549961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1068156150300495060133229 400558556362685647549961)
                      ·
                        rfl

theorem cell23_780085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_780085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780085 prefixEnd_780085 := by exact prefixLift 780085
  have htrace : WordTrace (prefixWord ++ tailWord_780085) baseStart_780085 baseEnd_780085 := by
    simpa [prefixWord, tailWord_780085, baseEnd_780085] using wordTrace_append hprefix tailTrace_780085
  have hstable : (prefixWord ++ tailWord_780085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780085).length < 2 ^ (prefixWord ++ tailWord_780085).sum := by decide
  have hdescent : baseEnd_780085 < baseStart_780085 := by decide
  rcases family_descends (prefixWord ++ tailWord_780085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780094 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_780094 : Nat := 118140960795 + 780094 * 2 ^ 59
def prefixEnd_780094 : Nat := 4983230072969 + 3 ^ 40 * 780094 * 2
def baseEnd_780094 : Nat := 400563177688576112337419

theorem tailTrace_780094 : CollatzResearch.WordTrace tailWord_780094 prefixEnd_780094 400563177688576112337419 := by
  unfold tailWord_780094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3556545704482517786671417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18968243757240094862247557 3556545704482517786671417)
  ·
    refine ⟨2667409278361888340003563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3556545704482517786671417 2667409278361888340003563)
    ·
      refine ⟨4001113917542832510005345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2667409278361888340003563 4001113917542832510005345)
      ·
        refine ⟨3000835438157124382504009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4001113917542832510005345 3000835438157124382504009)
        ·
          refine ⟨2250626578617843286878007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3000835438157124382504009 2250626578617843286878007)
          ·
            refine ⟨3375939867926764930317011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250626578617843286878007 3375939867926764930317011)
            ·
              refine ⟨5063909801890147395475517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375939867926764930317011 5063909801890147395475517)
              ·
                refine ⟨1898966175708805273303319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063909801890147395475517 1898966175708805273303319)
                ·
                  refine ⟨2848449263563207909954979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1898966175708805273303319 2848449263563207909954979)
                  ·
                    refine ⟨4272673895344811864932469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2848449263563207909954979 4272673895344811864932469)
                    ·
                      refine ⟨400563177688576112337419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4272673895344811864932469 400563177688576112337419)
                      ·
                        rfl

theorem cell23_780094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_780094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780094 prefixEnd_780094 := by exact prefixLift 780094
  have htrace : WordTrace (prefixWord ++ tailWord_780094) baseStart_780094 baseEnd_780094 := by
    simpa [prefixWord, tailWord_780094, baseEnd_780094] using wordTrace_append hprefix tailTrace_780094
  have hstable : (prefixWord ++ tailWord_780094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780094).length < 2 ^ (prefixWord ++ tailWord_780094).sum := by decide
  have hdescent : baseEnd_780094 < baseStart_780094 := by decide
  rcases family_descends (prefixWord ++ tailWord_780094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780157 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 2, 6]
def baseStart_780157 : Nat := 118140960795 + 780157 * 2 ^ 59
def prefixEnd_780157 : Nat := 4983230072969 + 3 ^ 40 * 780157 * 2
def baseEnd_780157 : Nat := 133531842323269788616543

theorem tailTrace_780157 : CollatzResearch.WordTrace tailWord_780157 prefixEnd_780157 133531842323269788616543 := by
  unfold tailWord_780157
  simp only [CollatzResearch.WordTrace]
  refine ⟨28454663434631904052914725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18969775623087936035276483 28454663434631904052914725)
  ·
    refine ⟨5335249393993482009921511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28454663434631904052914725 5335249393993482009921511)
    ·
      refine ⟨8002874090990223014882267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5335249393993482009921511 8002874090990223014882267)
      ·
        refine ⟨12004311136485334522323401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8002874090990223014882267 12004311136485334522323401)
        ·
          refine ⟨9003233352364000891742551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12004311136485334522323401 9003233352364000891742551)
          ·
            refine ⟨13504850028546001337613827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9003233352364000891742551 13504850028546001337613827)
            ·
              refine ⟨20257275042819002006420741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13504850028546001337613827 20257275042819002006420741)
              ·
                refine ⟨3798239070528562876203889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20257275042819002006420741 3798239070528562876203889)
                ·
                  refine ⟨2848679302896422157152917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3798239070528562876203889 2848679302896422157152917)
                  ·
                    refine ⟨133531842323269788616543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2848679302896422157152917 133531842323269788616543)
                    ·
                      rfl

theorem cell23_780157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_780157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780157 prefixEnd_780157 := by exact prefixLift 780157
  have htrace : WordTrace (prefixWord ++ tailWord_780157) baseStart_780157 baseEnd_780157 := by
    simpa [prefixWord, tailWord_780157, baseEnd_780157] using wordTrace_append hprefix tailTrace_780157
  have hstable : (prefixWord ++ tailWord_780157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780157).length < 2 ^ (prefixWord ++ tailWord_780157).sum := by decide
  have hdescent : baseEnd_780157 < baseStart_780157 := by decide
  rcases family_descends (prefixWord ++ tailWord_780157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780177 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_780177 : Nat := 118140960795 + 780177 * 2 ^ 59
def prefixEnd_780177 : Nat := 4983230072969 + 3 ^ 40 * 780177 * 2
def baseEnd_780177 : Nat := 400605796582899287599537

theorem tailTrace_780177 : CollatzResearch.WordTrace tailWord_780177 prefixEnd_780177 400605796582899287599537 := by
  unfold tailWord_780177
  simp only [CollatzResearch.WordTrace]
  refine ⟨28455392894559447468642785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18970261929706298312428523 28455392894559447468642785)
  ·
    refine ⟨21341544670919585601482089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28455392894559447468642785 21341544670919585601482089)
    ·
      refine ⟨16006158503189689201111567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21341544670919585601482089 16006158503189689201111567)
      ·
        refine ⟨24009237754784533801667351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16006158503189689201111567 24009237754784533801667351)
        ·
          refine ⟨36013856632176800702501027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24009237754784533801667351 36013856632176800702501027)
          ·
            refine ⟨54020784948265201053751541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36013856632176800702501027 54020784948265201053751541)
            ·
              refine ⟨5064448588899862598789207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54020784948265201053751541 5064448588899862598789207)
              ·
                refine ⟨7596672883349793898183811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5064448588899862598789207 7596672883349793898183811)
                ·
                  refine ⟨11395009325024690847275717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7596672883349793898183811 11395009325024690847275717)
                  ·
                    refine ⟨2136564248442129533864197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11395009325024690847275717 2136564248442129533864197)
                    ·
                      refine ⟨400605796582899287599537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2136564248442129533864197 400605796582899287599537)
                      ·
                        rfl

theorem cell23_780177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_780177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780177 prefixEnd_780177 := by exact prefixLift 780177
  have htrace : WordTrace (prefixWord ++ tailWord_780177) baseStart_780177 baseEnd_780177 := by
    simpa [prefixWord, tailWord_780177, baseEnd_780177] using wordTrace_append hprefix tailTrace_780177
  have hstable : (prefixWord ++ tailWord_780177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780177).length < 2 ^ (prefixWord ++ tailWord_780177).sum := by decide
  have hdescent : baseEnd_780177 < baseStart_780177 := by decide
  rcases family_descends (prefixWord ++ tailWord_780177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780181 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_780181 : Nat := 118140960795 + 780181 * 2 ^ 59
def prefixEnd_780181 : Nat := 4983230072969 + 3 ^ 40 * 780181 * 2
def baseEnd_780181 : Nat := 400607850505517271949519

theorem tailTrace_780181 : CollatzResearch.WordTrace tailWord_780181 prefixEnd_780181 400607850505517271949519 := by
  unfold tailWord_780181
  simp only [CollatzResearch.WordTrace]
  refine ⟨28455538786544956151788397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18970359191029970767858931 28455538786544956151788397)
  ·
    refine ⟨10670827044954358556920649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28455538786544956151788397 10670827044954358556920649)
    ·
      refine ⟨8003120283715768917690487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10670827044954358556920649 8003120283715768917690487)
      ·
        refine ⟨12004680425573653376535731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8003120283715768917690487 12004680425573653376535731)
        ·
          refine ⟨18007020638360480064803597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12004680425573653376535731 18007020638360480064803597)
          ·
            refine ⟨6752632739385180024301349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18007020638360480064803597 6752632739385180024301349)
            ·
              refine ⟨1266118638634721254556503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6752632739385180024301349 1266118638634721254556503)
              ·
                refine ⟨1899177957952081881834755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266118638634721254556503 1899177957952081881834755)
                ·
                  refine ⟨2848766936928122822752133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1899177957952081881834755 2848766936928122822752133)
                  ·
                    refine ⟨534143800674023029266025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2848766936928122822752133 534143800674023029266025)
                    ·
                      refine ⟨400607850505517271949519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 534143800674023029266025 400607850505517271949519)
                      ·
                        rfl

theorem cell23_780181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_780181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780181 prefixEnd_780181 := by exact prefixLift 780181
  have htrace : WordTrace (prefixWord ++ tailWord_780181) baseStart_780181 baseEnd_780181 := by
    simpa [prefixWord, tailWord_780181, baseEnd_780181] using wordTrace_append hprefix tailTrace_780181
  have hstable : (prefixWord ++ tailWord_780181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780181).length < 2 ^ (prefixWord ++ tailWord_780181).sum := by decide
  have hdescent : baseEnd_780181 < baseStart_780181 := by decide
  rcases family_descends (prefixWord ++ tailWord_780181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780221 : List Nat := [1, 4, 1, 2, 3, 1, 2, 4, 5]
def baseStart_780221 : Nat := 118140960795 + 780221 * 2 ^ 59
def prefixEnd_780221 : Nat := 4983230072969 + 3 ^ 40 * 780221 * 2
def baseEnd_780221 : Nat := 44514265525744123938815

theorem tailTrace_780221 : CollatzResearch.WordTrace tailWord_780221 prefixEnd_780221 44514265525744123938815 := by
  unfold tailWord_780221
  simp only [CollatzResearch.WordTrace]
  refine ⟨28456997706400042983244517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18971331804266695322163011 28456997706400042983244517)
  ·
    refine ⟨5335687069950008059358347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28456997706400042983244517 5335687069950008059358347)
    ·
      refine ⟨8003530604925012089037521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5335687069950008059358347 8003530604925012089037521)
      ·
        refine ⟨6002647953693759066778141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8003530604925012089037521 6002647953693759066778141)
        ·
          refine ⟨2250992982635159650041803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6002647953693759066778141 2250992982635159650041803)
          ·
            refine ⟨3376489473952739475062705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250992982635159650041803 3376489473952739475062705)
            ·
              refine ⟨2532367105464554606297029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376489473952739475062705 2532367105464554606297029)
              ·
                refine ⟨474818832274603988680693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2532367105464554606297029 474818832274603988680693)
                ·
                  refine ⟨44514265525744123938815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 474818832274603988680693 44514265525744123938815)
                  ·
                    rfl

theorem cell23_780221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_780221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780221 prefixEnd_780221 := by exact prefixLift 780221
  have htrace : WordTrace (prefixWord ++ tailWord_780221) baseStart_780221 baseEnd_780221 := by
    simpa [prefixWord, tailWord_780221, baseEnd_780221] using wordTrace_append hprefix tailTrace_780221
  have hstable : (prefixWord ++ tailWord_780221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780221).length < 2 ^ (prefixWord ++ tailWord_780221).sum := by decide
  have hdescent : baseEnd_780221 < baseStart_780221 := by decide
  rcases family_descends (prefixWord ++ tailWord_780221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780247 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 2, 8]
def baseStart_780247 : Nat := 118140960795 + 780247 * 2 ^ 59
def prefixEnd_780247 : Nat := 4983230072969 + 3 ^ 40 * 780247 * 2
def baseEnd_780247 : Nat := 133547246742904671241405

theorem tailTrace_780247 : CollatzResearch.WordTrace tailWord_780247 prefixEnd_780247 133547246742904671241405 := by
  unfold tailWord_780247
  simp only [CollatzResearch.WordTrace]
  refine ⟨28457946004305849423690995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18971964002870566282460663 28457946004305849423690995)
  ·
    refine ⟨42686919006458774135536493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28457946004305849423690995 42686919006458774135536493)
    ·
      refine ⟨16007594627422040300826185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42686919006458774135536493 16007594627422040300826185)
      ·
        refine ⟨12005695970566530225619639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16007594627422040300826185 12005695970566530225619639)
        ·
          refine ⟨18008543955849795338429459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12005695970566530225619639 18008543955849795338429459)
          ·
            refine ⟨27012815933774693007644189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18008543955849795338429459 27012815933774693007644189)
            ·
              refine ⟨10129805975165509877866571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27012815933774693007644189 10129805975165509877866571)
              ·
                refine ⟨15194708962748264816799857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10129805975165509877866571 15194708962748264816799857)
                ·
                  refine ⟨11396031722061198612599893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15194708962748264816799857 11396031722061198612599893)
                  ·
                    refine ⟨133547246742904671241405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11396031722061198612599893 133547246742904671241405)
                    ·
                      rfl

theorem cell23_780247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_780247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780247 prefixEnd_780247 := by exact prefixLift 780247
  have htrace : WordTrace (prefixWord ++ tailWord_780247) baseStart_780247 baseEnd_780247 := by
    simpa [prefixWord, tailWord_780247, baseEnd_780247] using wordTrace_append hprefix tailTrace_780247
  have hstable : (prefixWord ++ tailWord_780247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780247).length < 2 ^ (prefixWord ++ tailWord_780247).sum := by decide
  have hdescent : baseEnd_780247 < baseStart_780247 := by decide
  rcases family_descends (prefixWord ++ tailWord_780247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780267 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 6]
def baseStart_780267 : Nat := 118140960795 + 780267 * 2 ^ 59
def prefixEnd_780267 : Nat := 4983230072969 + 3 ^ 40 * 780267 * 2
def baseEnd_780267 : Nat := 400652009841803935474123

theorem tailTrace_780267 : CollatzResearch.WordTrace tailWord_780267 prefixEnd_780267 400652009841803935474123 := by
  unfold tailWord_780267
  simp only [CollatzResearch.WordTrace]
  refine ⟨28458675464233392839419055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18972450309488928559612703 28458675464233392839419055)
  ·
    refine ⟨42688013196350089259128583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28458675464233392839419055 42688013196350089259128583)
    ·
      refine ⟨64032019794525133888692875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42688013196350089259128583 64032019794525133888692875)
      ·
        refine ⟨96048029691787700833039313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64032019794525133888692875 96048029691787700833039313)
        ·
          refine ⟨72036022268840775624779485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96048029691787700833039313 72036022268840775624779485)
          ·
            refine ⟨27013508350815290859292307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72036022268840775624779485 27013508350815290859292307)
            ·
              refine ⟨40520262526222936288938461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27013508350815290859292307 40520262526222936288938461)
              ·
                refine ⟨15195098447333601108351923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40520262526222936288938461 15195098447333601108351923)
                ·
                  refine ⟨22792647671000401662527885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15195098447333601108351923 22792647671000401662527885)
                  ·
                    refine ⟨8547242876625150623447957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22792647671000401662527885 8547242876625150623447957)
                    ·
                      refine ⟨400652009841803935474123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8547242876625150623447957 400652009841803935474123)
                      ·
                        rfl

theorem cell23_780267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_780267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780267 prefixEnd_780267 := by exact prefixLift 780267
  have htrace : WordTrace (prefixWord ++ tailWord_780267) baseStart_780267 baseEnd_780267 := by
    simpa [prefixWord, tailWord_780267, baseEnd_780267] using wordTrace_append hprefix tailTrace_780267
  have hstable : (prefixWord ++ tailWord_780267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780267).length < 2 ^ (prefixWord ++ tailWord_780267).sum := by decide
  have hdescent : baseEnd_780267 < baseStart_780267 := by decide
  rcases family_descends (prefixWord ++ tailWord_780267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780281 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 3, 4]
def baseStart_780281 : Nat := 118140960795 + 780281 * 2 ^ 59
def prefixEnd_780281 : Nat := 4983230072969 + 3 ^ 40 * 780281 * 2
def baseEnd_780281 : Nat := 133553066190322293566353

theorem tailTrace_780281 : CollatzResearch.WordTrace tailWord_780281 prefixEnd_780281 133553066190322293566353 := by
  unfold tailWord_780281
  simp only [CollatzResearch.WordTrace]
  refine ⟨28459186086182673230428697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18972790724121782153619131 28459186086182673230428697)
  ·
    refine ⟨21344389564637004922821523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28459186086182673230428697 21344389564637004922821523)
    ·
      refine ⟨32016584346955507384232285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21344389564637004922821523 32016584346955507384232285)
      ·
        refine ⟨12006219130108315269087107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32016584346955507384232285 12006219130108315269087107)
        ·
          refine ⟨18009328695162472903630661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12006219130108315269087107 18009328695162472903630661)
          ·
            refine ⟨3376749130342963669430749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18009328695162472903630661 3376749130342963669430749)
            ·
              refine ⟨1266280923878611376036531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3376749130342963669430749 1266280923878611376036531)
              ·
                refine ⟨1899421385817917064054797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266280923878611376036531 1899421385817917064054797)
                ·
                  refine ⟨712283019681718899020549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1899421385817917064054797 712283019681718899020549)
                  ·
                    refine ⟨133553066190322293566353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 712283019681718899020549 133553066190322293566353)
                    ·
                      rfl

theorem cell23_780281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 4].length) (baseStart_780281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780281 prefixEnd_780281 := by exact prefixLift 780281
  have htrace : WordTrace (prefixWord ++ tailWord_780281) baseStart_780281 baseEnd_780281 := by
    simpa [prefixWord, tailWord_780281, baseEnd_780281] using wordTrace_append hprefix tailTrace_780281
  have hstable : (prefixWord ++ tailWord_780281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780281).length < 2 ^ (prefixWord ++ tailWord_780281).sum := by decide
  have hdescent : baseEnd_780281 < baseStart_780281 := by decide
  rcases family_descends (prefixWord ++ tailWord_780281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780331 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 4, 3, 2]
def baseStart_780331 : Nat := 118140960795 + 780331 * 2 ^ 59
def prefixEnd_780331 : Nat := 4983230072969 + 3 ^ 40 * 780331 * 2
def baseEnd_780331 : Nat := 400684872603691685073829

theorem tailTrace_780331 : CollatzResearch.WordTrace tailWord_780331 prefixEnd_780331 400684872603691685073829 := by
  unfold tailWord_780331
  simp only [CollatzResearch.WordTrace]
  refine ⟨28461009736001531769748847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18974006490667687846499231 28461009736001531769748847)
  ·
    refine ⟨42691514604002297654623271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28461009736001531769748847 42691514604002297654623271)
    ·
      refine ⟨64037271906003446481934907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42691514604002297654623271 64037271906003446481934907)
      ·
        refine ⟨96055907859005169722902361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64037271906003446481934907 96055907859005169722902361)
        ·
          refine ⟨72041930894253877292176771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96055907859005169722902361 72041930894253877292176771)
          ·
            refine ⟨108062896341380815938265157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72041930894253877292176771 108062896341380815938265157)
            ·
              refine ⟨20261793064008902988424717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108062896341380815938265157 20261793064008902988424717)
              ·
                refine ⟨7598172399003338620659269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20261793064008902988424717 7598172399003338620659269)
                ·
                  refine ⟨1424657324813125991373613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7598172399003338620659269 1424657324813125991373613)
                  ·
                    refine ⟨534246496804922246765105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1424657324813125991373613 534246496804922246765105)
                    ·
                      refine ⟨400684872603691685073829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 534246496804922246765105 400684872603691685073829)
                      ·
                        rfl

theorem cell23_780331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 3, 2].length) (baseStart_780331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780331 prefixEnd_780331 := by exact prefixLift 780331
  have htrace : WordTrace (prefixWord ++ tailWord_780331) baseStart_780331 baseEnd_780331 := by
    simpa [prefixWord, tailWord_780331, baseEnd_780331] using wordTrace_append hprefix tailTrace_780331
  have hstable : (prefixWord ++ tailWord_780331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780331).length < 2 ^ (prefixWord ++ tailWord_780331).sum := by decide
  have hdescent : baseEnd_780331 < baseStart_780331 := by decide
  rcases family_descends (prefixWord ++ tailWord_780331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780358 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_780358 : Nat := 118140960795 + 780358 * 2 ^ 59
def prefixEnd_780358 : Nat := 4983230072969 + 3 ^ 40 * 780358 * 2
def baseEnd_780358 : Nat := 133566245527121026478735

theorem tailTrace_780358 : CollatzResearch.WordTrace tailWord_780358 prefixEnd_780358 133566245527121026478735 := by
  unfold tailWord_780358
  simp only [CollatzResearch.WordTrace]
  refine ⟨889437328340741105655679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18974663004602476920654485 889437328340741105655679)
  ·
    refine ⟨1334155992511111658483519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 889437328340741105655679 1334155992511111658483519)
    ·
      refine ⟨2001233988766667487725279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334155992511111658483519 2001233988766667487725279)
      ·
        refine ⟨3001850983150001231587919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001233988766667487725279 3001850983150001231587919)
        ·
          refine ⟨4502776474725001847381879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3001850983150001231587919 4502776474725001847381879)
          ·
            refine ⟨6754164712087502771072819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4502776474725001847381879 6754164712087502771072819)
            ·
              refine ⟨10131247068131254156609229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6754164712087502771072819 10131247068131254156609229)
              ·
                refine ⟨3799217650549220308728461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10131247068131254156609229 3799217650549220308728461)
                ·
                  refine ⟨1424706618955957615773173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3799217650549220308728461 1424706618955957615773173)
                  ·
                    refine ⟨133566245527121026478735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1424706618955957615773173 133566245527121026478735)
                    ·
                      rfl

theorem cell23_780358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_780358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780358 prefixEnd_780358 := by exact prefixLift 780358
  have htrace : WordTrace (prefixWord ++ tailWord_780358) baseStart_780358 baseEnd_780358 := by
    simpa [prefixWord, tailWord_780358, baseEnd_780358] using wordTrace_append hprefix tailTrace_780358
  have hstable : (prefixWord ++ tailWord_780358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780358).length < 2 ^ (prefixWord ++ tailWord_780358).sum := by decide
  have hdescent : baseEnd_780358 < baseStart_780358 := by decide
  rcases family_descends (prefixWord ++ tailWord_780358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780361 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 4]
def baseStart_780361 : Nat := 118140960795 + 780361 * 2 ^ 59
def prefixEnd_780361 : Nat := 4983230072969 + 3 ^ 40 * 780361 * 2
def baseEnd_780361 : Nat := 400700277023326567698691

theorem tailTrace_780361 : CollatzResearch.WordTrace tailWord_780361 prefixEnd_780361 400700277023326567698691 := by
  unfold tailWord_780361
  simp only [CollatzResearch.WordTrace]
  refine ⟨28462103925892846893340937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18974735950595231262227291 28462103925892846893340937)
  ·
    refine ⟨21346577944419635170005703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28462103925892846893340937 21346577944419635170005703)
    ·
      refine ⟨32019866916629452755008555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21346577944419635170005703 32019866916629452755008555)
      ·
        refine ⟨48029800374944179132512833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32019866916629452755008555 48029800374944179132512833)
        ·
          refine ⟨36022350281208134349384625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48029800374944179132512833 36022350281208134349384625)
          ·
            refine ⟨27016762710906100762038469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36022350281208134349384625 27016762710906100762038469)
            ·
              refine ⟨5065643008294893892882213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27016762710906100762038469 5065643008294893892882213)
              ·
                refine ⟨949808064055292604915415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5065643008294893892882213 949808064055292604915415)
                ·
                  refine ⟨1424712096082938907373123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 949808064055292604915415 1424712096082938907373123)
                  ·
                    refine ⟨2137068144124408361059685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1424712096082938907373123 2137068144124408361059685)
                    ·
                      refine ⟨400700277023326567698691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2137068144124408361059685 400700277023326567698691)
                      ·
                        rfl

theorem cell23_780361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 1, 4].length) (baseStart_780361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780361 prefixEnd_780361 := by exact prefixLift 780361
  have htrace : WordTrace (prefixWord ++ tailWord_780361) baseStart_780361 baseEnd_780361 := by
    simpa [prefixWord, tailWord_780361, baseEnd_780361] using wordTrace_append hprefix tailTrace_780361
  have hstable : (prefixWord ++ tailWord_780361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780361).length < 2 ^ (prefixWord ++ tailWord_780361).sum := by decide
  have hdescent : baseEnd_780361 < baseStart_780361 := by decide
  rcases family_descends (prefixWord ++ tailWord_780361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780378 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2]
def baseStart_780378 : Nat := 118140960795 + 780378 * 2 ^ 59
def prefixEnd_780378 : Nat := 4983230072969 + 3 ^ 40 * 780378 * 2
def baseEnd_780378 : Nat := 400709006194453001186113

theorem tailTrace_780378 : CollatzResearch.WordTrace tailWord_780378 prefixEnd_780378 400709006194453001186113 := by
  unfold tailWord_780378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115680991707814699177447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18975149311220839197806525 7115680991707814699177447)
  ·
    refine ⟨10673521487561722048766171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7115680991707814699177447 10673521487561722048766171)
    ·
      refine ⟨16010282231342583073149257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10673521487561722048766171 16010282231342583073149257)
      ·
        refine ⟨12007711673506937304861943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16010282231342583073149257 12007711673506937304861943)
        ·
          refine ⟨18011567510260405957292915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12007711673506937304861943 18011567510260405957292915)
          ·
            refine ⟨27017351265390608935939373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18011567510260405957292915 27017351265390608935939373)
            ·
              refine ⟨10131506724521478350977265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27017351265390608935939373 10131506724521478350977265)
              ·
                refine ⟨7598630043391108763232949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10131506724521478350977265 7598630043391108763232949)
                ·
                  refine ⟨712371566567916446553089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7598630043391108763232949 712371566567916446553089)
                  ·
                    refine ⟨534278674925937334914817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 712371566567916446553089 534278674925937334914817)
                    ·
                      refine ⟨400709006194453001186113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 534278674925937334914817 400709006194453001186113)
                      ·
                        rfl

theorem cell23_780378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_780378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780378 prefixEnd_780378 := by exact prefixLift 780378
  have htrace : WordTrace (prefixWord ++ tailWord_780378) baseStart_780378 baseEnd_780378 := by
    simpa [prefixWord, tailWord_780378, baseEnd_780378] using wordTrace_append hprefix tailTrace_780378
  have hstable : (prefixWord ++ tailWord_780378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780378).length < 2 ^ (prefixWord ++ tailWord_780378).sum := by decide
  have hdescent : baseEnd_780378 < baseStart_780378 := by decide
  rcases family_descends (prefixWord ++ tailWord_780378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780384 : List Nat := [2, 1, 1, 3, 2, 4, 10]
def baseStart_780384 : Nat := 118140960795 + 780384 * 2 ^ 59
def prefixEnd_780384 : Nat := 4983230072969 + 3 ^ 40 * 780384 * 2
def baseEnd_780384 : Nat := 4947062803436789848285

theorem tailTrace_780384 : CollatzResearch.WordTrace tailWord_780384 prefixEnd_780384 4947062803436789848285 := by
  unfold tailWord_780384
  simp only [CollatzResearch.WordTrace]
  refine ⟨14231471402404760910714103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18975295203206347880952137 14231471402404760910714103)
  ·
    refine ⟨21347207103607141366071155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14231471402404760910714103 21347207103607141366071155)
    ·
      refine ⟨32020810655410712049106733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21347207103607141366071155 32020810655410712049106733)
      ·
        refine ⟨12007803995779017018415025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32020810655410712049106733 12007803995779017018415025)
        ·
          refine ⟨9005852996834262763811269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12007803995779017018415025 9005852996834262763811269)
          ·
            refine ⟨1688597436906424268214613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9005852996834262763811269 1688597436906424268214613)
            ·
              refine ⟨4947062803436789848285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1688597436906424268214613 4947062803436789848285)
              ·
                rfl

theorem cell23_780384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 10].length) (baseStart_780384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780384 prefixEnd_780384 := by exact prefixLift 780384
  have htrace : WordTrace (prefixWord ++ tailWord_780384) baseStart_780384 baseEnd_780384 := by
    simpa [prefixWord, tailWord_780384, baseEnd_780384] using wordTrace_append hprefix tailTrace_780384
  have hstable : (prefixWord ++ tailWord_780384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780384).length < 2 ^ (prefixWord ++ tailWord_780384).sum := by decide
  have hdescent : baseEnd_780384 < baseStart_780384 := by decide
  rcases family_descends (prefixWord ++ tailWord_780384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780388 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_780388 : Nat := 118140960795 + 780388 * 2 ^ 59
def prefixEnd_780388 : Nat := 4983230072969 + 3 ^ 40 * 780388 * 2
def baseEnd_780388 : Nat := 133571380333665987353689

theorem tailTrace_780388 : CollatzResearch.WordTrace tailWord_780388 prefixEnd_780388 133571380333665987353689 := by
  unfold tailWord_780388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14231544348397515252286909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18975392464530020336382545 14231544348397515252286909)
  ·
    refine ⟨5336829130649068219607591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14231544348397515252286909 5336829130649068219607591)
    ·
      refine ⟨8005243695973602329411387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5336829130649068219607591 8005243695973602329411387)
      ·
        refine ⟨12007865543960403494117081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8005243695973602329411387 12007865543960403494117081)
        ·
          refine ⟨9005899157970302620587811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12007865543960403494117081 9005899157970302620587811)
          ·
            refine ⟨13508848736955453930881717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9005899157970302620587811 13508848736955453930881717)
            ·
              refine ⟨1266454569089573806020161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13508848736955453930881717 1266454569089573806020161)
              ·
                refine ⟨949840926817180354515121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266454569089573806020161 949840926817180354515121)
                ·
                  refine ⟨712380695112885265886341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 949840926817180354515121 712380695112885265886341)
                  ·
                    refine ⟨133571380333665987353689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 712380695112885265886341 133571380333665987353689)
                    ·
                      rfl

theorem cell23_780388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_780388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780388 prefixEnd_780388 := by exact prefixLift 780388
  have htrace : WordTrace (prefixWord ++ tailWord_780388) baseStart_780388 baseEnd_780388 := by
    simpa [prefixWord, tailWord_780388, baseEnd_780388] using wordTrace_append hprefix tailTrace_780388
  have hstable : (prefixWord ++ tailWord_780388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780388).length < 2 ^ (prefixWord ++ tailWord_780388).sum := by decide
  have hdescent : baseEnd_780388 < baseStart_780388 := by decide
  rcases family_descends (prefixWord ++ tailWord_780388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780446 : List Nat := [4, 3, 1, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_780446 : Nat := 118140960795 + 780446 * 2 ^ 59
def prefixEnd_780446 : Nat := 4983230072969 + 3 ^ 40 * 780446 * 2
def baseEnd_780446 : Nat := 400743922878958735135801

theorem tailTrace_780446 : CollatzResearch.WordTrace tailWord_780446 prefixEnd_780446 400743922878958735135801 := by
  unfold tailWord_780446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3558150516323113301273149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18976802753723270940123461 3558150516323113301273149)
  ·
    refine ⟨1334306443621167487977431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3558150516323113301273149 1334306443621167487977431)
    ·
      refine ⟨2001459665431751231966147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334306443621167487977431 2001459665431751231966147)
      ·
        refine ⟨3002189498147626847949221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001459665431751231966147 3002189498147626847949221)
        ·
          refine ⟨562910530902680033990479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3002189498147626847949221 562910530902680033990479)
          ·
            refine ⟨844365796354020050985719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562910530902680033990479 844365796354020050985719)
            ·
              refine ⟨1266548694531030076478579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844365796354020050985719 1266548694531030076478579)
              ·
                refine ⟨1899823041796545114717869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266548694531030076478579 1899823041796545114717869)
                ·
                  refine ⟨712433640673704418019201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1899823041796545114717869 712433640673704418019201)
                  ·
                    refine ⟨534325230505278313514401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 712433640673704418019201 534325230505278313514401)
                    ·
                      refine ⟨400743922878958735135801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 534325230505278313514401 400743922878958735135801)
                      ·
                        rfl

theorem cell23_780446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_780446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780446 prefixEnd_780446 := by exact prefixLift 780446
  have htrace : WordTrace (prefixWord ++ tailWord_780446) baseStart_780446 baseEnd_780446 := by
    simpa [prefixWord, tailWord_780446, baseEnd_780446] using wordTrace_append hprefix tailTrace_780446
  have hstable : (prefixWord ++ tailWord_780446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780446).length < 2 ^ (prefixWord ++ tailWord_780446).sum := by decide
  have hdescent : baseEnd_780446 < baseStart_780446 := by decide
  rcases family_descends (prefixWord ++ tailWord_780446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780471 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_780471 : Nat := 118140960795 + 780471 * 2 ^ 59
def prefixEnd_780471 : Nat := 4983230072969 + 3 ^ 40 * 780471 * 2
def baseEnd_780471 : Nat := 400756759895321137323185

theorem tailTrace_780471 : CollatzResearch.WordTrace tailWord_780471 prefixEnd_780471 400756759895321137323185 := by
  unfold tailWord_780471
  simp only [CollatzResearch.WordTrace]
  refine ⟨28466115955494335679845267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18977410636996223786563511 28466115955494335679845267)
  ·
    refine ⟨42699173933241503519767901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28466115955494335679845267 42699173933241503519767901)
    ·
      refine ⟨16012190224965563819912963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42699173933241503519767901 16012190224965563819912963)
      ·
        refine ⟨24018285337448345729869445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16012190224965563819912963 24018285337448345729869445)
        ·
          refine ⟨4503428500771564824350521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24018285337448345729869445 4503428500771564824350521)
          ·
            refine ⟨3377571375578673618262891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4503428500771564824350521 3377571375578673618262891)
            ·
              refine ⟨5066357063368010427394337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377571375578673618262891 5066357063368010427394337)
              ·
                refine ⟨3799767797526007820545753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5066357063368010427394337 3799767797526007820545753)
                ·
                  refine ⟨2849825848144505865409315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3799767797526007820545753 2849825848144505865409315)
                  ·
                    refine ⟨4274738772216758798113973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2849825848144505865409315 4274738772216758798113973)
                    ·
                      refine ⟨400756759895321137323185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4274738772216758798113973 400756759895321137323185)
                      ·
                        rfl

theorem cell23_780471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_780471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780471 prefixEnd_780471 := by exact prefixLift 780471
  have htrace : WordTrace (prefixWord ++ tailWord_780471) baseStart_780471 baseEnd_780471 := by
    simpa [prefixWord, tailWord_780471, baseEnd_780471] using wordTrace_append hprefix tailTrace_780471
  have hstable : (prefixWord ++ tailWord_780471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780471).length < 2 ^ (prefixWord ++ tailWord_780471).sum := by decide
  have hdescent : baseEnd_780471 < baseStart_780471 := by decide
  rcases family_descends (prefixWord ++ tailWord_780471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780515 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 4]
def baseStart_780515 : Nat := 118140960795 + 780515 * 2 ^ 59
def prefixEnd_780515 : Nat := 4983230072969 + 3 ^ 40 * 780515 * 2
def baseEnd_780515 : Nat := 400779353044118965172983

theorem tailTrace_780515 : CollatzResearch.WordTrace tailWord_780515 prefixEnd_780515 400779353044118965172983 := by
  unfold tailWord_780515
  simp only [CollatzResearch.WordTrace]
  refine ⟨28467720767334931194446999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18978480511556620796297999 28467720767334931194446999)
  ·
    refine ⟨42701581151002396791670499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28467720767334931194446999 42701581151002396791670499)
    ·
      refine ⟨64052371726503595187505749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42701581151002396791670499 64052371726503595187505749)
      ·
        refine ⟨750613731169964006103583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 64052371726503595187505749 750613731169964006103583)
        ·
          refine ⟨1125920596754946009155375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750613731169964006103583 1125920596754946009155375)
          ·
            refine ⟨1688880895132419013733063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125920596754946009155375 1688880895132419013733063)
            ·
              refine ⟨2533321342698628520599595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1688880895132419013733063 2533321342698628520599595)
              ·
                refine ⟨3799982014047942780899393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533321342698628520599595 3799982014047942780899393)
                ·
                  refine ⟨2849986510535957085674545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3799982014047942780899393 2849986510535957085674545)
                  ·
                    refine ⟨2137489882901967814255909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2849986510535957085674545 2137489882901967814255909)
                    ·
                      refine ⟨400779353044118965172983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2137489882901967814255909 400779353044118965172983)
                      ·
                        rfl

theorem cell23_780515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_780515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780515 prefixEnd_780515 := by exact prefixLift 780515
  have htrace : WordTrace (prefixWord ++ tailWord_780515) baseStart_780515 baseEnd_780515 := by
    simpa [prefixWord, tailWord_780515, baseEnd_780515] using wordTrace_append hprefix tailTrace_780515
  have hstable : (prefixWord ++ tailWord_780515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780515).length < 2 ^ (prefixWord ++ tailWord_780515).sum := by decide
  have hdescent : baseEnd_780515 < baseStart_780515 := by decide
  rcases family_descends (prefixWord ++ tailWord_780515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780538 : List Nat := [3, 1, 1, 1, 1, 5, 3, 1, 2, 5]
def baseStart_780538 : Nat := 118140960795 + 780538 * 2 ^ 59
def prefixEnd_780538 : Nat := 4983230072969 + 3 ^ 40 * 780538 * 2
def baseEnd_780538 : Nat := 133597054366390791728459

theorem tailTrace_780538 : CollatzResearch.WordTrace tailWord_780538 prefixEnd_780538 133597054366390791728459 := by
  unfold tailWord_780538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7117139911562901530633567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18979039764167737415022845 7117139911562901530633567)
  ·
    refine ⟨10675709867344352295950351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7117139911562901530633567 10675709867344352295950351)
    ·
      refine ⟨16013564801016528443925527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10675709867344352295950351 16013564801016528443925527)
      ·
        refine ⟨24020347201524792665888291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16013564801016528443925527 24020347201524792665888291)
        ·
          refine ⟨36030520802287188998832437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24020347201524792665888291 36030520802287188998832437)
          ·
            refine ⟨3377861325214423968640541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36030520802287188998832437 3377861325214423968640541)
            ·
              refine ⟨1266697996955408988240203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3377861325214423968640541 1266697996955408988240203)
              ·
                refine ⟨1900046995433113482360305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266697996955408988240203 1900046995433113482360305)
                ·
                  refine ⟨1425035246574835111770229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1900046995433113482360305 1425035246574835111770229)
                  ·
                    refine ⟨133597054366390791728459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1425035246574835111770229 133597054366390791728459)
                    ·
                      rfl

theorem cell23_780538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_780538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780538 prefixEnd_780538 := by exact prefixLift 780538
  have htrace : WordTrace (prefixWord ++ tailWord_780538) baseStart_780538 baseEnd_780538 := by
    simpa [prefixWord, tailWord_780538, baseEnd_780538] using wordTrace_append hprefix tailTrace_780538
  have hstable : (prefixWord ++ tailWord_780538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780538).length < 2 ^ (prefixWord ++ tailWord_780538).sum := by decide
  have hdescent : baseEnd_780538 < baseStart_780538 := by decide
  rcases family_descends (prefixWord ++ tailWord_780538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780558 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_780558 : Nat := 118140960795 + 780558 * 2 ^ 59
def prefixEnd_780558 : Nat := 4983230072969 + 3 ^ 40 * 780558 * 2
def baseEnd_780558 : Nat := 400801432712262296935285

theorem tailTrace_780558 : CollatzResearch.WordTrace tailWord_780558 prefixEnd_780558 400801432712262296935285 := by
  unfold tailWord_780558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3558661138272393692282791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18979526070786099692174885 3558661138272393692282791)
  ·
    refine ⟨5337991707408590538424187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3558661138272393692282791 5337991707408590538424187)
    ·
      refine ⟨8006987561112885807636281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5337991707408590538424187 8006987561112885807636281)
      ·
        refine ⟨6005240670834664355727211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8006987561112885807636281 6005240670834664355727211)
        ·
          refine ⟨9007861006251996533590817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6005240670834664355727211 9007861006251996533590817)
          ·
            refine ⟨6755895754688997400193113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9007861006251996533590817 6755895754688997400193113)
            ·
              refine ⟨5066921816016748050144835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6755895754688997400193113 5066921816016748050144835)
              ·
                refine ⟨7600382724025122075217253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5066921816016748050144835 7600382724025122075217253)
                ·
                  refine ⟨1425071760754710389103235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7600382724025122075217253 1425071760754710389103235)
                  ·
                    refine ⟨2137607641132065583654853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1425071760754710389103235 2137607641132065583654853)
                    ·
                      refine ⟨400801432712262296935285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2137607641132065583654853 400801432712262296935285)
                      ·
                        rfl

theorem cell23_780558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_780558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780558 prefixEnd_780558 := by exact prefixLift 780558
  have htrace : WordTrace (prefixWord ++ tailWord_780558) baseStart_780558 baseEnd_780558 := by
    simpa [prefixWord, tailWord_780558, baseEnd_780558] using wordTrace_append hprefix tailTrace_780558
  have hstable : (prefixWord ++ tailWord_780558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780558).length < 2 ^ (prefixWord ++ tailWord_780558).sum := by decide
  have hdescent : baseEnd_780558 < baseStart_780558 := by decide
  rcases family_descends (prefixWord ++ tailWord_780558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780575 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 2, 4, 2]
def baseStart_780575 : Nat := 118140960795 + 780575 * 2 ^ 59
def prefixEnd_780575 : Nat := 4983230072969 + 3 ^ 40 * 780575 * 2
def baseEnd_780575 : Nat := 400810161883388730422707

theorem tailTrace_780575 : CollatzResearch.WordTrace tailWord_780575 prefixEnd_780575 400810161883388730422707 := by
  unfold tailWord_780575
  simp only [CollatzResearch.WordTrace]
  refine ⟨28469909147117561441631179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18979939431411707627754119 28469909147117561441631179)
  ·
    refine ⟨42704863720676342162446769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28469909147117561441631179 42704863720676342162446769)
    ·
      refine ⟨32028647790507256621835077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42704863720676342162446769 32028647790507256621835077)
      ·
        refine ⟨6005371460720110616594077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32028647790507256621835077 6005371460720110616594077)
        ·
          refine ⟨2252014297770041481222779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6005371460720110616594077 2252014297770041481222779)
          ·
            refine ⟨3378021446655062221834169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252014297770041481222779 3378021446655062221834169)
            ·
              refine ⟨2533516084991296666375627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378021446655062221834169 2533516084991296666375627)
              ·
                refine ⟨3800274127486944999563441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533516084991296666375627 3800274127486944999563441)
                ·
                  refine ⟨2850205595615208749672581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3800274127486944999563441 2850205595615208749672581)
                  ·
                    refine ⟨534413549177851640563609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2850205595615208749672581 534413549177851640563609)
                    ·
                      refine ⟨400810161883388730422707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 534413549177851640563609 400810161883388730422707)
                      ·
                        rfl

theorem cell23_780575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_780575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780575 prefixEnd_780575 := by exact prefixLift 780575
  have htrace : WordTrace (prefixWord ++ tailWord_780575) baseStart_780575 baseEnd_780575 := by
    simpa [prefixWord, tailWord_780575, baseEnd_780575] using wordTrace_append hprefix tailTrace_780575
  have hstable : (prefixWord ++ tailWord_780575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780575).length < 2 ^ (prefixWord ++ tailWord_780575).sum := by decide
  have hdescent : baseEnd_780575 < baseStart_780575 := by decide
  rcases family_descends (prefixWord ++ tailWord_780575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780602 : List Nat := [3, 1, 1, 1, 4, 2, 3, 3, 1, 4]
def baseStart_780602 : Nat := 118140960795 + 780602 * 2 ^ 59
def prefixEnd_780602 : Nat := 4983230072969 + 3 ^ 40 * 780602 * 2
def baseEnd_780602 : Nat := 133608008620353374928361

theorem tailTrace_780602 : CollatzResearch.WordTrace tailWord_780602 prefixEnd_780602 133608008620353374928361 := by
  unfold tailWord_780602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7117723479504936263216015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18980595945346496701909373 7117723479504936263216015)
  ·
    refine ⟨10676585219257404394824023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7117723479504936263216015 10676585219257404394824023)
    ·
      refine ⟨16014877828886106592236035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10676585219257404394824023 16014877828886106592236035)
      ·
        refine ⟨24022316743329159888354053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16014877828886106592236035 24022316743329159888354053)
        ·
          refine ⟨4504184389374217479066385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24022316743329159888354053 4504184389374217479066385)
          ·
            refine ⟨3378138292030663109299789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4504184389374217479066385 3378138292030663109299789)
            ·
              refine ⟨1266801859511498665987421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3378138292030663109299789 1266801859511498665987421)
              ·
                refine ⟨475050697316811999745283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1266801859511498665987421 475050697316811999745283)
                ·
                  refine ⟨712576045975217999617925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475050697316811999745283 712576045975217999617925)
                  ·
                    refine ⟨133608008620353374928361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 712576045975217999617925 133608008620353374928361)
                    ·
                      rfl

theorem cell23_780602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 4].length) (baseStart_780602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780602 prefixEnd_780602 := by exact prefixLift 780602
  have htrace : WordTrace (prefixWord ++ tailWord_780602) baseStart_780602 baseEnd_780602 := by
    simpa [prefixWord, tailWord_780602, baseEnd_780602] using wordTrace_append hprefix tailTrace_780602
  have hstable : (prefixWord ++ tailWord_780602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780602).length < 2 ^ (prefixWord ++ tailWord_780602).sum := by decide
  have hdescent : baseEnd_780602 < baseStart_780602 := by decide
  rcases family_descends (prefixWord ++ tailWord_780602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780645 : List Nat := [1, 3, 1, 3, 1, 3, 3, 2, 1, 5]
def baseStart_780645 : Nat := 118140960795 + 780645 * 2 ^ 59
def prefixEnd_780645 : Nat := 4983230072969 + 3 ^ 40 * 780645 * 2
def baseEnd_780645 : Nat := 133615368509734485515795

theorem tailTrace_780645 : CollatzResearch.WordTrace tailWord_780645 prefixEnd_780645 133615368509734485515795 := by
  unfold tailWord_780645
  simp only [CollatzResearch.WordTrace]
  refine ⟨28472462256863963396679389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18981641504575975597786259 28472462256863963396679389)
  ·
    refine ⟨10677173346323986273754771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28472462256863963396679389 10677173346323986273754771)
    ·
      refine ⟨16015760019485979410632157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10677173346323986273754771 16015760019485979410632157)
      ·
        refine ⟨6005910007307242278987059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16015760019485979410632157 6005910007307242278987059)
        ·
          refine ⟨9008865010960863418480589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6005910007307242278987059 9008865010960863418480589)
          ·
            refine ⟨3378324379110323781930221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9008865010960863418480589 3378324379110323781930221)
            ·
              refine ⟨1266871642166371418223833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3378324379110323781930221 1266871642166371418223833)
              ·
                refine ⟨950153731624778563667875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266871642166371418223833 950153731624778563667875)
                ·
                  refine ⟨1425230597437167845501813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950153731624778563667875 1425230597437167845501813)
                  ·
                    refine ⟨133615368509734485515795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1425230597437167845501813 133615368509734485515795)
                    ·
                      rfl

theorem cell23_780645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_780645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780645 prefixEnd_780645 := by exact prefixLift 780645
  have htrace : WordTrace (prefixWord ++ tailWord_780645) baseStart_780645 baseEnd_780645 := by
    simpa [prefixWord, tailWord_780645, baseEnd_780645] using wordTrace_append hprefix tailTrace_780645
  have hstable : (prefixWord ++ tailWord_780645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780645).length < 2 ^ (prefixWord ++ tailWord_780645).sum := by decide
  have hdescent : baseEnd_780645 < baseStart_780645 := by decide
  rcases family_descends (prefixWord ++ tailWord_780645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780658 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 3, 6]
def baseStart_780658 : Nat := 118140960795 + 780658 * 2 ^ 59
def prefixEnd_780658 : Nat := 4983230072969 + 3 ^ 40 * 780658 * 2
def baseEnd_780658 : Nat := 133617593592570635228275

theorem tailTrace_780658 : CollatzResearch.WordTrace tailWord_780658 prefixEnd_780658 133617593592570635228275 := by
  unfold tailWord_780658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7118234101454216654225657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18981957603877911077935085 7118234101454216654225657)
  ·
    refine ⟨5338675576090662490669243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7118234101454216654225657 5338675576090662490669243)
    ·
      refine ⟨8008013364135993736003865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5338675576090662490669243 8008013364135993736003865)
      ·
        refine ⟨6006010023101995302002899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8008013364135993736003865 6006010023101995302002899)
        ·
          refine ⟨9009015034652992953004349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6006010023101995302002899 9009015034652992953004349)
          ·
            refine ⟨3378380637994872357376631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9009015034652992953004349 3378380637994872357376631)
            ·
              refine ⟨5067570956992308536064947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3378380637994872357376631 5067570956992308536064947)
              ·
                refine ⟨7601356435488462804097421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5067570956992308536064947 7601356435488462804097421)
                ·
                  refine ⟨2850508663308173551536533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7601356435488462804097421 2850508663308173551536533)
                  ·
                    refine ⟨133617593592570635228275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2850508663308173551536533 133617593592570635228275)
                    ·
                      rfl

theorem cell23_780658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_780658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780658 prefixEnd_780658 := by exact prefixLift 780658
  have htrace : WordTrace (prefixWord ++ tailWord_780658) baseStart_780658 baseEnd_780658 := by
    simpa [prefixWord, tailWord_780658, baseEnd_780658] using wordTrace_append hprefix tailTrace_780658
  have hstable : (prefixWord ++ tailWord_780658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780658).length < 2 ^ (prefixWord ++ tailWord_780658).sum := by decide
  have hdescent : baseEnd_780658 < baseStart_780658 := by decide
  rcases family_descends (prefixWord ++ tailWord_780658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780668 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_780668 : Nat := 118140960795 + 780668 * 2 ^ 59
def prefixEnd_780668 : Nat := 4983230072969 + 3 ^ 40 * 780668 * 2
def baseEnd_780668 : Nat := 400857915584256866559779

theorem tailTrace_780668 : CollatzResearch.WordTrace tailWord_780668 prefixEnd_780668 400857915584256866559779 := by
  unfold tailWord_780668
  simp only [CollatzResearch.WordTrace]
  refine ⟨14236650567890319162383329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18982200757187092216511105 14236650567890319162383329)
  ·
    refine ⟨10677487925917739371787497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14236650567890319162383329 10677487925917739371787497)
    ·
      refine ⟨8008115944438304528840623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10677487925917739371787497 8008115944438304528840623)
      ·
        refine ⟨12012173916657456793260935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8008115944438304528840623 12012173916657456793260935)
        ·
          refine ⟨18018260874986185189891403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12012173916657456793260935 18018260874986185189891403)
          ·
            refine ⟨27027391312479277784837105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18018260874986185189891403 27027391312479277784837105)
            ·
              refine ⟨20270543484359458338627829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27027391312479277784837105 20270543484359458338627829)
              ·
                refine ⟨1900363451658699219246359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20270543484359458338627829 1900363451658699219246359)
                ·
                  refine ⟨2850545177488048828869539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900363451658699219246359 2850545177488048828869539)
                  ·
                    refine ⟨4275817766232073243304309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2850545177488048828869539 4275817766232073243304309)
                    ·
                      refine ⟨400857915584256866559779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4275817766232073243304309 400857915584256866559779)
                      ·
                        rfl

theorem cell23_780668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_780668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780668 prefixEnd_780668 := by exact prefixLift 780668
  have htrace : WordTrace (prefixWord ++ tailWord_780668) baseStart_780668 baseEnd_780668 := by
    simpa [prefixWord, tailWord_780668, baseEnd_780668] using wordTrace_append hprefix tailTrace_780668
  have hstable : (prefixWord ++ tailWord_780668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780668).length < 2 ^ (prefixWord ++ tailWord_780668).sum := by decide
  have hdescent : baseEnd_780668 < baseStart_780668 := by decide
  rcases family_descends (prefixWord ++ tailWord_780668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780692 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_780692 : Nat := 118140960795 + 780692 * 2 ^ 59
def prefixEnd_780692 : Nat := 4983230072969 + 3 ^ 40 * 780692 * 2
def baseEnd_780692 : Nat := 133623413039988257553223

theorem tailTrace_780692 : CollatzResearch.WordTrace tailWord_780692 prefixEnd_780692 133623413039988257553223 := by
  unfold tailWord_780692
  simp only [CollatzResearch.WordTrace]
  refine ⟨14237088243846845211820165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18982784325129126949093553 14237088243846845211820165)
  ·
    refine ⟨2669454045721283477216281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14237088243846845211820165 2669454045721283477216281)
    ·
      refine ⟨2002090534290962607912211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2669454045721283477216281 2002090534290962607912211)
      ·
        refine ⟨3003135801436443911868317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002090534290962607912211 3003135801436443911868317)
        ·
          refine ⟨1126175925538666466950619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3003135801436443911868317 1126175925538666466950619)
          ·
            refine ⟨1689263888307999700425929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126175925538666466950619 1689263888307999700425929)
            ·
              refine ⟨1266947916230999775319447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1689263888307999700425929 1266947916230999775319447)
              ·
                refine ⟨1900421874346499662979171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266947916230999775319447 1900421874346499662979171)
                ·
                  refine ⟨2850632811519749494468757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900421874346499662979171 2850632811519749494468757)
                  ·
                    refine ⟨133623413039988257553223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2850632811519749494468757 133623413039988257553223)
                    ·
                      rfl

theorem cell23_780692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_780692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780692 prefixEnd_780692 := by exact prefixLift 780692
  have htrace : WordTrace (prefixWord ++ tailWord_780692) baseStart_780692 baseEnd_780692 := by
    simpa [prefixWord, tailWord_780692, baseEnd_780692] using wordTrace_append hprefix tailTrace_780692
  have hstable : (prefixWord ++ tailWord_780692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780692).length < 2 ^ (prefixWord ++ tailWord_780692).sum := by decide
  have hdescent : baseEnd_780692 < baseStart_780692 := by decide
  rcases family_descends (prefixWord ++ tailWord_780692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780712 : List Nat := [2, 1, 6, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_780712 : Nat := 118140960795 + 780712 * 2 ^ 59
def prefixEnd_780712 : Nat := 4983230072969 + 3 ^ 40 * 780712 * 2
def baseEnd_780712 : Nat := 400880508733054694409577

theorem tailTrace_780712 : CollatzResearch.WordTrace tailWord_780712 prefixEnd_780712 400880508733054694409577 := by
  unfold tailWord_780712
  simp only [CollatzResearch.WordTrace]
  refine ⟨14237452973810616919684195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18983270631747489226245593 14237452973810616919684195)
  ·
    refine ⟨21356179460715925379526293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14237452973810616919684195 21356179460715925379526293)
    ·
      refine ⟨1001070912221059002165295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21356179460715925379526293 1001070912221059002165295)
      ·
        refine ⟨1501606368331588503247943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001070912221059002165295 1501606368331588503247943)
        ·
          refine ⟨2252409552497382754871915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501606368331588503247943 2252409552497382754871915)
          ·
            refine ⟨3378614328746074132307873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252409552497382754871915 3378614328746074132307873)
            ·
              refine ⟨2533960746559555599230905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378614328746074132307873 2533960746559555599230905)
              ·
                refine ⟨1900470559919666699423179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533960746559555599230905 1900470559919666699423179)
                ·
                  refine ⟨2850705839879500049134769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900470559919666699423179 2850705839879500049134769)
                  ·
                    refine ⟨2138029379909625036851077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2850705839879500049134769 2138029379909625036851077)
                    ·
                      refine ⟨400880508733054694409577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2138029379909625036851077 400880508733054694409577)
                      ·
                        rfl

theorem cell23_780712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_780712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780712 prefixEnd_780712 := by exact prefixLift 780712
  have htrace : WordTrace (prefixWord ++ tailWord_780712) baseStart_780712 baseEnd_780712 := by
    simpa [prefixWord, tailWord_780712, baseEnd_780712] using wordTrace_append hprefix tailTrace_780712
  have hstable : (prefixWord ++ tailWord_780712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780712).length < 2 ^ (prefixWord ++ tailWord_780712).sum := by decide
  have hdescent : baseEnd_780712 < baseStart_780712 := by decide
  rcases family_descends (prefixWord ++ tailWord_780712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780775 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_780775 : Nat := 118140960795 + 780775 * 2 ^ 59
def prefixEnd_780775 : Nat := 4983230072969 + 3 ^ 40 * 780775 * 2
def baseEnd_780775 : Nat := 400912858014287947921787

theorem tailTrace_780775 : CollatzResearch.WordTrace tailWord_780775 prefixEnd_780775 400912858014287947921787 := by
  unfold tailWord_780775
  simp only [CollatzResearch.WordTrace]
  refine ⟨28477203746392995598911779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18984802497595330399274519 28477203746392995598911779)
  ·
    refine ⟨42715805619589493398367669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28477203746392995598911779 42715805619589493398367669)
    ·
      refine ⟨4004606776836515006096969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42715805619589493398367669 4004606776836515006096969)
      ·
        refine ⟨3003455082627386254572727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4004606776836515006096969 3003455082627386254572727)
        ·
          refine ⟨4505182623941079381859091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003455082627386254572727 4505182623941079381859091)
          ·
            refine ⟨6757773935911619072788637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4505182623941079381859091 6757773935911619072788637)
            ·
              refine ⟨2534165225966857152295739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6757773935911619072788637 2534165225966857152295739)
              ·
                refine ⟨3801247838950285728443609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2534165225966857152295739 3801247838950285728443609)
                ·
                  refine ⟨2850935879212714296332707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3801247838950285728443609 2850935879212714296332707)
                  ·
                    refine ⟨4276403818819071444499061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2850935879212714296332707 4276403818819071444499061)
                    ·
                      refine ⟨400912858014287947921787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4276403818819071444499061 400912858014287947921787)
                      ·
                        rfl

theorem cell23_780775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_780775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780775 prefixEnd_780775 := by exact prefixLift 780775
  have htrace : WordTrace (prefixWord ++ tailWord_780775) baseStart_780775 baseEnd_780775 := by
    simpa [prefixWord, tailWord_780775, baseEnd_780775] using wordTrace_append hprefix tailTrace_780775
  have hstable : (prefixWord ++ tailWord_780775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780775).length < 2 ^ (prefixWord ++ tailWord_780775).sum := by decide
  have hdescent : baseEnd_780775 < baseStart_780775 := by decide
  rcases family_descends (prefixWord ++ tailWord_780775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780805 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_780805 : Nat := 118140960795 + 780805 * 2 ^ 59
def prefixEnd_780805 : Nat := 4983230072969 + 3 ^ 40 * 780805 * 2
def baseEnd_780805 : Nat := 400928262433922830546649

theorem tailTrace_780805 : CollatzResearch.WordTrace tailWord_780805 prefixEnd_780805 400928262433922830546649 := by
  unfold tailWord_780805
  simp only [CollatzResearch.WordTrace]
  refine ⟨28478297936284310722503869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18985531957522873815002579 28478297936284310722503869)
  ·
    refine ⟨10679361726106616520938951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28478297936284310722503869 10679361726106616520938951)
    ·
      refine ⟨16019042589159924781408427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10679361726106616520938951 16019042589159924781408427)
      ·
        refine ⟨24028563883739887172112641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16019042589159924781408427 24028563883739887172112641)
        ·
          refine ⟨18021422912804915379084481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24028563883739887172112641 18021422912804915379084481)
          ·
            refine ⟨13516067184603686534313361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18021422912804915379084481 13516067184603686534313361)
            ·
              refine ⟨10137050388452764900735021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13516067184603686534313361 10137050388452764900735021)
              ·
                refine ⟨3801393895669786837775633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10137050388452764900735021 3801393895669786837775633)
                ·
                  refine ⟨2851045421752340128331725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3801393895669786837775633 2851045421752340128331725)
                  ·
                    refine ⟨1069142033157127548124397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2851045421752340128331725 1069142033157127548124397)
                    ·
                      refine ⟨400928262433922830546649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1069142033157127548124397 400928262433922830546649)
                      ·
                        rfl

theorem cell23_780805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_780805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780805 prefixEnd_780805 := by exact prefixLift 780805
  have htrace : WordTrace (prefixWord ++ tailWord_780805) baseStart_780805 baseEnd_780805 := by
    simpa [prefixWord, tailWord_780805, baseEnd_780805] using wordTrace_append hprefix tailTrace_780805
  have hstable : (prefixWord ++ tailWord_780805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780805).length < 2 ^ (prefixWord ++ tailWord_780805).sum := by decide
  have hdescent : baseEnd_780805 < baseStart_780805 := by decide
  rcases family_descends (prefixWord ++ tailWord_780805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780835 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 5]
def baseStart_780835 : Nat := 118140960795 + 780835 * 2 ^ 59
def prefixEnd_780835 : Nat := 4983230072969 + 3 ^ 40 * 780835 * 2
def baseEnd_780835 : Nat := 400943666853557713171511

theorem tailTrace_780835 : CollatzResearch.WordTrace tailWord_780835 prefixEnd_780835 400943666853557713171511 := by
  unfold tailWord_780835
  simp only [CollatzResearch.WordTrace]
  refine ⟨28479392126175625846095959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18986261417450417230730639 28479392126175625846095959)
  ·
    refine ⟨42719088189263438769143939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28479392126175625846095959 42719088189263438769143939)
    ·
      refine ⟨64078632283895158153715909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42719088189263438769143939 64078632283895158153715909)
      ·
        refine ⟨12014743553230342153821733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64078632283895158153715909 12014743553230342153821733)
        ·
          refine ⟨2252764416230689153841575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12014743553230342153821733 2252764416230689153841575)
          ·
            refine ⟨3379146624346033730762363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252764416230689153841575 3379146624346033730762363)
            ·
              refine ⟨5068719936519050596143545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379146624346033730762363 5068719936519050596143545)
              ·
                refine ⟨3801539952389287947107659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5068719936519050596143545 3801539952389287947107659)
                ·
                  refine ⟨5702309928583931920661489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801539952389287947107659 5702309928583931920661489)
                  ·
                    refine ⟨4276732446437948940496117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5702309928583931920661489 4276732446437948940496117)
                    ·
                      refine ⟨400943666853557713171511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4276732446437948940496117 400943666853557713171511)
                      ·
                        rfl

theorem cell23_780835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_780835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780835 prefixEnd_780835 := by exact prefixLift 780835
  have htrace : WordTrace (prefixWord ++ tailWord_780835) baseStart_780835 baseEnd_780835 := by
    simpa [prefixWord, tailWord_780835, baseEnd_780835] using wordTrace_append hprefix tailTrace_780835
  have hstable : (prefixWord ++ tailWord_780835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780835).length < 2 ^ (prefixWord ++ tailWord_780835).sum := by decide
  have hdescent : baseEnd_780835 < baseStart_780835 := by decide
  rcases family_descends (prefixWord ++ tailWord_780835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780842 : List Nat := [3, 1, 4, 1, 1, 2, 2, 2, 2, 5]
def baseStart_780842 : Nat := 118140960795 + 780842 * 2 ^ 59
def prefixEnd_780842 : Nat := 4983230072969 + 3 ^ 40 * 780842 * 2
def baseEnd_780842 : Nat := 133649087072713061927993

theorem tailTrace_780842 : CollatzResearch.WordTrace tailWord_780842 prefixEnd_780842 133649087072713061927993 := by
  unfold tailWord_780842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7119911859287566510400195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18986431624766844027733853 7119911859287566510400195)
  ·
    refine ⟨10679867788931349765600293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7119911859287566510400195 10679867788931349765600293)
    ·
      refine ⟨2002475210424628081050055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10679867788931349765600293 2002475210424628081050055)
      ·
        refine ⟨3003712815636942121575083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002475210424628081050055 3003712815636942121575083)
        ·
          refine ⟨4505569223455413182362625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003712815636942121575083 4505569223455413182362625)
          ·
            refine ⟨3379176917591559886771969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4505569223455413182362625 3379176917591559886771969)
            ·
              refine ⟨2534382688193669915078977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3379176917591559886771969 2534382688193669915078977)
              ·
                refine ⟨1900787016145252436309233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534382688193669915078977 1900787016145252436309233)
                ·
                  refine ⟨1425590262108939327231925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1900787016145252436309233 1425590262108939327231925)
                  ·
                    refine ⟨133649087072713061927993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1425590262108939327231925 133649087072713061927993)
                    ·
                      rfl

theorem cell23_780842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_780842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780842 prefixEnd_780842 := by exact prefixLift 780842
  have htrace : WordTrace (prefixWord ++ tailWord_780842) baseStart_780842 baseEnd_780842 := by
    simpa [prefixWord, tailWord_780842, baseEnd_780842] using wordTrace_append hprefix tailTrace_780842
  have hstable : (prefixWord ++ tailWord_780842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780842).length < 2 ^ (prefixWord ++ tailWord_780842).sum := by decide
  have hdescent : baseEnd_780842 < baseStart_780842 := by decide
  rcases family_descends (prefixWord ++ tailWord_780842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780882 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_780882 : Nat := 118140960795 + 780882 * 2 ^ 59
def prefixEnd_780882 : Nat := 4983230072969 + 3 ^ 40 * 780882 * 2
def baseEnd_780882 : Nat := 400967800444319029283795

theorem tailTrace_780882 : CollatzResearch.WordTrace tailWord_780882 prefixEnd_780882 400967800444319029283795 := by
  unfold tailWord_780882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7120276589251338218264225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18987404238003568582037933 7120276589251338218264225)
  ·
    refine ⟨5340207441938503663698169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7120276589251338218264225 5340207441938503663698169)
    ·
      refine ⟨4005155581453877747773627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5340207441938503663698169 4005155581453877747773627)
      ·
        refine ⟨6007733372180816621660441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005155581453877747773627 6007733372180816621660441)
        ·
          refine ⟨4505800029135612466245331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6007733372180816621660441 4505800029135612466245331)
          ·
            refine ⟨6758700043703418699367997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4505800029135612466245331 6758700043703418699367997)
            ·
              refine ⟨2534512516388782012262999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6758700043703418699367997 2534512516388782012262999)
              ·
                refine ⟨3801768774583173018394499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2534512516388782012262999 3801768774583173018394499)
                ·
                  refine ⟨5702653161874759527591749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3801768774583173018394499 5702653161874759527591749)
                  ·
                    refine ⟨1069247467851517411423453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5702653161874759527591749 1069247467851517411423453)
                    ·
                      refine ⟨400967800444319029283795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1069247467851517411423453 400967800444319029283795)
                      ·
                        rfl

theorem cell23_780882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_780882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780882 prefixEnd_780882 := by exact prefixLift 780882
  have htrace : WordTrace (prefixWord ++ tailWord_780882) baseStart_780882 baseEnd_780882 := by
    simpa [prefixWord, tailWord_780882, baseEnd_780882] using wordTrace_append hprefix tailTrace_780882
  have hstable : (prefixWord ++ tailWord_780882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780882).length < 2 ^ (prefixWord ++ tailWord_780882).sum := by decide
  have hdescent : baseEnd_780882 < baseStart_780882 := by decide
  rcases family_descends (prefixWord ++ tailWord_780882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780895 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 3]
def baseStart_780895 : Nat := 118140960795 + 780895 * 2 ^ 59
def prefixEnd_780895 : Nat := 4983230072969 + 3 ^ 40 * 780895 * 2
def baseEnd_780895 : Nat := 400974475692827478421235

theorem tailTrace_780895 : CollatzResearch.WordTrace tailWord_780895 prefixEnd_780895 400974475692827478421235 := by
  unfold tailWord_780895
  simp only [CollatzResearch.WordTrace]
  refine ⟨28481580505958256093280139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18987720337305504062186759 28481580505958256093280139)
  ·
    refine ⟨42722370758937384139920209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28481580505958256093280139 42722370758937384139920209)
    ·
      refine ⟨32041778069203038104940157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42722370758937384139920209 32041778069203038104940157)
      ·
        refine ⟨12015666775951139289352559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32041778069203038104940157 12015666775951139289352559)
        ·
          refine ⟨18023500163926708934028839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12015666775951139289352559 18023500163926708934028839)
          ·
            refine ⟨27035250245890063401043259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18023500163926708934028839 27035250245890063401043259)
            ·
              refine ⟨40552875368835095101564889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27035250245890063401043259 40552875368835095101564889)
              ·
                refine ⟨30414656526626321326173667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40552875368835095101564889 30414656526626321326173667)
                ·
                  refine ⟨45621984789939481989260501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30414656526626321326173667 45621984789939481989260501)
                  ·
                    refine ⟨1069265268514206609123293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45621984789939481989260501 1069265268514206609123293)
                    ·
                      refine ⟨400974475692827478421235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1069265268514206609123293 400974475692827478421235)
                      ·
                        rfl

theorem cell23_780895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_780895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780895 prefixEnd_780895 := by exact prefixLift 780895
  have htrace : WordTrace (prefixWord ++ tailWord_780895) baseStart_780895 baseEnd_780895 := by
    simpa [prefixWord, tailWord_780895, baseEnd_780895] using wordTrace_append hprefix tailTrace_780895
  have hstable : (prefixWord ++ tailWord_780895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780895).length < 2 ^ (prefixWord ++ tailWord_780895).sum := by decide
  have hdescent : baseEnd_780895 < baseStart_780895 := by decide
  rcases family_descends (prefixWord ++ tailWord_780895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780915 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 3, 5]
def baseStart_780915 : Nat := 118140960795 + 780915 * 2 ^ 59
def prefixEnd_780915 : Nat := 4983230072969 + 3 ^ 40 * 780915 * 2
def baseEnd_780915 : Nat := 133661581768639133390381

theorem tailTrace_780915 : CollatzResearch.WordTrace tailWord_780915 prefixEnd_780915 133661581768639133390381 := by
  unfold tailWord_780915
  simp only [CollatzResearch.WordTrace]
  refine ⟨28482309965885799509008199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18988206643923866339338799 28482309965885799509008199)
  ·
    refine ⟨42723464948828699263512299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28482309965885799509008199 42723464948828699263512299)
    ·
      refine ⟨64085197423243048895268449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42723464948828699263512299 64085197423243048895268449)
      ·
        refine ⟨48063898067432286671451337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64085197423243048895268449 48063898067432286671451337)
        ·
          refine ⟨36047923550574215003588503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48063898067432286671451337 36047923550574215003588503)
          ·
            refine ⟨54071885325861322505382755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36047923550574215003588503 54071885325861322505382755)
            ·
              refine ⟨81107827988791983758074133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54071885325861322505382755 81107827988791983758074133)
              ·
                refine ⟨3801929436974624238659725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81107827988791983758074133 3801929436974624238659725)
                ·
                  refine ⟨1425723538865484089497397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3801929436974624238659725 1425723538865484089497397)
                  ·
                    refine ⟨133661581768639133390381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1425723538865484089497397 133661581768639133390381)
                    ·
                      rfl

theorem cell23_780915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 5].length) (baseStart_780915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780915 prefixEnd_780915 := by exact prefixLift 780915
  have htrace : WordTrace (prefixWord ++ tailWord_780915) baseStart_780915 baseEnd_780915 := by
    simpa [prefixWord, tailWord_780915, baseEnd_780915] using wordTrace_append hprefix tailTrace_780915
  have hstable : (prefixWord ++ tailWord_780915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780915).length < 2 ^ (prefixWord ++ tailWord_780915).sum := by decide
  have hdescent : baseEnd_780915 < baseStart_780915 := by decide
  rcases family_descends (prefixWord ++ tailWord_780915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780929 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_780929 : Nat := 118140960795 + 780929 * 2 ^ 59
def prefixEnd_780929 : Nat := 4983230072969 + 3 ^ 40 * 780929 * 2
def baseEnd_780929 : Nat := 400991934035080345396079

theorem tailTrace_780929 : CollatzResearch.WordTrace tailWord_780929 prefixEnd_780929 400991934035080345396079 := by
  unfold tailWord_780929
  simp only [CollatzResearch.WordTrace]
  refine ⟨28482820587835079900017841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18988547058556719933345227 28482820587835079900017841)
  ·
    refine ⟨21362115440876309925013381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28482820587835079900017841 21362115440876309925013381)
    ·
      refine ⟨4005396645164308110940009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21362115440876309925013381 4005396645164308110940009)
      ·
        refine ⟨3004047483873231083205007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4005396645164308110940009 3004047483873231083205007)
        ·
          refine ⟨4506071225809846624807511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004047483873231083205007 4506071225809846624807511)
          ·
            refine ⟨6759106838714769937211267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4506071225809846624807511 6759106838714769937211267)
            ·
              refine ⟨10138660258072154905816901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6759106838714769937211267 10138660258072154905816901)
              ·
                refine ⟨1900998798388529044840669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10138660258072154905816901 1900998798388529044840669)
                ·
                  refine ⟨712874549395698391815251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1900998798388529044840669 712874549395698391815251)
                  ·
                    refine ⟨1069311824093547587722877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 712874549395698391815251 1069311824093547587722877)
                    ·
                      refine ⟨400991934035080345396079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1069311824093547587722877 400991934035080345396079)
                      ·
                        rfl

theorem cell23_780929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_780929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780929 prefixEnd_780929 := by exact prefixLift 780929
  have htrace : WordTrace (prefixWord ++ tailWord_780929) baseStart_780929 baseEnd_780929 := by
    simpa [prefixWord, tailWord_780929, baseEnd_780929] using wordTrace_append hprefix tailTrace_780929
  have hstable : (prefixWord ++ tailWord_780929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780929).length < 2 ^ (prefixWord ++ tailWord_780929).sum := by decide
  have hdescent : baseEnd_780929 < baseStart_780929 := by decide
  rcases family_descends (prefixWord ++ tailWord_780929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780956 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_780956 : Nat := 118140960795 + 780956 * 2 ^ 59
def prefixEnd_780956 : Nat := 4983230072969 + 3 ^ 40 * 780956 * 2
def baseEnd_780956 : Nat := 401005798012751739758455

theorem tailTrace_780956 : CollatzResearch.WordTrace tailWord_780956 prefixEnd_780956 401005798012751739758455 := by
  unfold tailWord_780956
  simp only [CollatzResearch.WordTrace]
  refine ⟨14241902679368631755625361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18989203572491509007500481 14241902679368631755625361)
  ·
    refine ⟨10681427009526473816719021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14241902679368631755625361 10681427009526473816719021)
    ·
      refine ⟨4005535128572427681269633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10681427009526473816719021 4005535128572427681269633)
      ·
        refine ⟨3004151346429320760952225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4005535128572427681269633 3004151346429320760952225)
        ·
          refine ⟨2253113509821990570714169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3004151346429320760952225 2253113509821990570714169)
          ·
            refine ⟨1689835132366492928035627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2253113509821990570714169 1689835132366492928035627)
            ·
              refine ⟨2534752698549739392053441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689835132366492928035627 2534752698549739392053441)
              ·
                refine ⟨1901064523912304544040081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534752698549739392053441 1901064523912304544040081)
                ·
                  refine ⟨1425798392934228408030061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1901064523912304544040081 1425798392934228408030061)
                  ·
                    refine ⟨534674397350335653011273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425798392934228408030061 534674397350335653011273)
                    ·
                      refine ⟨401005798012751739758455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 534674397350335653011273 401005798012751739758455)
                      ·
                        rfl

theorem cell23_780956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_780956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780956 prefixEnd_780956 := by exact prefixLift 780956
  have htrace : WordTrace (prefixWord ++ tailWord_780956) baseStart_780956 baseEnd_780956 := by
    simpa [prefixWord, tailWord_780956, baseEnd_780956] using wordTrace_append hprefix tailTrace_780956
  have hstable : (prefixWord ++ tailWord_780956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780956).length < 2 ^ (prefixWord ++ tailWord_780956).sum := by decide
  have hdescent : baseEnd_780956 < baseStart_780956 := by decide
  rcases family_descends (prefixWord ++ tailWord_780956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780970 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 6]
def baseStart_780970 : Nat := 118140960795 + 780970 * 2 ^ 59
def prefixEnd_780970 : Nat := 4983230072969 + 3 ^ 40 * 780970 * 2
def baseEnd_780970 : Nat := 44556998526879409442599

theorem tailTrace_780970 : CollatzResearch.WordTrace tailWord_780970 prefixEnd_780970 44556998526879409442599 := by
  unfold tailWord_780970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121078995171635975565091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18989543987124362601506909 7121078995171635975565091)
  ·
    refine ⟨10681618492757453963347637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7121078995171635975565091 10681618492757453963347637)
    ·
      refine ⟨1001401733696011309063841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10681618492757453963347637 1001401733696011309063841)
      ·
        refine ⟨751051300272008481797881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1001401733696011309063841 751051300272008481797881)
        ·
          refine ⟨563288475204006361348411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751051300272008481797881 563288475204006361348411)
          ·
            refine ⟨844932712806009542022617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563288475204006361348411 844932712806009542022617)
            ·
              refine ⟨633699534604507156516963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844932712806009542022617 633699534604507156516963)
              ·
                refine ⟨950549301906760734775445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633699534604507156516963 950549301906760734775445)
                ·
                  refine ⟨44556998526879409442599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 950549301906760734775445 44556998526879409442599)
                  ·
                    rfl

theorem cell23_780970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_780970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780970 prefixEnd_780970 := by exact prefixLift 780970
  have htrace : WordTrace (prefixWord ++ tailWord_780970) baseStart_780970 baseEnd_780970 := by
    simpa [prefixWord, tailWord_780970, baseEnd_780970] using wordTrace_append hprefix tailTrace_780970
  have hstable : (prefixWord ++ tailWord_780970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780970).length < 2 ^ (prefixWord ++ tailWord_780970).sum := by decide
  have hdescent : baseEnd_780970 < baseStart_780970 := by decide
  rcases family_descends (prefixWord ++ tailWord_780970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780975 : List Nat := [1, 1, 2, 1, 2, 5, 1, 10]
def baseStart_780975 : Nat := 118140960795 + 780975 * 2 ^ 59
def prefixEnd_780975 : Nat := 4983230072969 + 3 ^ 40 * 780975 * 2
def baseEnd_780975 : Nat := 14852427931303228348921

theorem tailTrace_780975 : CollatzResearch.WordTrace tailWord_780975 prefixEnd_780975 14852427931303228348921 := by
  unfold tailWord_780975
  simp only [CollatzResearch.WordTrace]
  refine ⟨28484498345668429756192379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18989665563778953170794919 28484498345668429756192379)
  ·
    refine ⟨42726747518502644634288569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28484498345668429756192379 42726747518502644634288569)
    ·
      refine ⟨32045060638876983475716427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42726747518502644634288569 32045060638876983475716427)
      ·
        refine ⟨48067590958315475213574641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32045060638876983475716427 48067590958315475213574641)
        ·
          refine ⟨36050693218736606410180981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48067590958315475213574641 36050693218736606410180981)
          ·
            refine ⟨3379752489256556850954467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36050693218736606410180981 3379752489256556850954467)
            ·
              refine ⟨5069628733884835276431701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3379752489256556850954467 5069628733884835276431701)
              ·
                refine ⟨14852427931303228348921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5069628733884835276431701 14852427931303228348921)
                ·
                  rfl

theorem cell23_780975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 10].length) (baseStart_780975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780975 prefixEnd_780975 := by exact prefixLift 780975
  have htrace : WordTrace (prefixWord ++ tailWord_780975) baseStart_780975 baseEnd_780975 := by
    simpa [prefixWord, tailWord_780975, baseEnd_780975] using wordTrace_append hprefix tailTrace_780975
  have hstable : (prefixWord ++ tailWord_780975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780975).length < 2 ^ (prefixWord ++ tailWord_780975).sum := by decide
  have hdescent : baseEnd_780975 < baseStart_780975 := by decide
  rcases family_descends (prefixWord ++ tailWord_780975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780979 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 2, 4]
def baseStart_780979 : Nat := 118140960795 + 780979 * 2 ^ 59
def prefixEnd_780979 : Nat := 4983230072969 + 3 ^ 40 * 780979 * 2
def baseEnd_780979 : Nat := 133672536022601716590283

theorem tailTrace_780979 : CollatzResearch.WordTrace tailWord_780979 prefixEnd_780979 133672536022601716590283 := by
  unfold tailWord_780979
  simp only [CollatzResearch.WordTrace]
  refine ⟨28484644237653938439337991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18989762825102625626225327 28484644237653938439337991)
  ·
    refine ⟨42726966356480907659006987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28484644237653938439337991 42726966356480907659006987)
    ·
      refine ⟨64090449534721361488510481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42726966356480907659006987 64090449534721361488510481)
      ·
        refine ⟨48067837151041021116382861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64090449534721361488510481 48067837151041021116382861)
        ·
          refine ⟨18025438931640382918643573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48067837151041021116382861 18025438931640382918643573)
          ·
            refine ⟨1689884899841285898622835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18025438931640382918643573 1689884899841285898622835)
            ·
              refine ⟨2534827349761928847934253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689884899841285898622835 2534827349761928847934253)
              ·
                refine ⟨950560256160723317975345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2534827349761928847934253 950560256160723317975345)
                ·
                  refine ⟨712920192120542488481509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 950560256160723317975345 712920192120542488481509)
                  ·
                    refine ⟨133672536022601716590283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 712920192120542488481509 133672536022601716590283)
                    ·
                      rfl

theorem cell23_780979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 4].length) (baseStart_780979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780979 prefixEnd_780979 := by exact prefixLift 780979
  have htrace : WordTrace (prefixWord ++ tailWord_780979) baseStart_780979 baseEnd_780979 := by
    simpa [prefixWord, tailWord_780979, baseEnd_780979] using wordTrace_append hprefix tailTrace_780979
  have hstable : (prefixWord ++ tailWord_780979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780979).length < 2 ^ (prefixWord ++ tailWord_780979).sum := by decide
  have hdescent : baseEnd_780979 < baseStart_780979 := by decide
  rcases family_descends (prefixWord ++ tailWord_780979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_780989 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_780989 : Nat := 118140960795 + 780989 * 2 ^ 59
def prefixEnd_780989 : Nat := 4983230072969 + 3 ^ 40 * 780989 * 2
def baseEnd_780989 : Nat := 401022742874350110645803

theorem tailTrace_780989 : CollatzResearch.WordTrace tailWord_780989 prefixEnd_780989 401022742874350110645803 := by
  unfold tailWord_780989
  simp only [CollatzResearch.WordTrace]
  refine ⟨28485008967617710147202021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18990005978411806764801347 28485008967617710147202021)
  ·
    refine ⟨5340939181428320652600379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28485008967617710147202021 5340939181428320652600379)
    ·
      refine ⟨8011408772142480978900569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5340939181428320652600379 8011408772142480978900569)
      ·
        refine ⟨6008556579106860734175427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8011408772142480978900569 6008556579106860734175427)
        ·
          refine ⟨9012834868660291101263141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008556579106860734175427 9012834868660291101263141)
          ·
            refine ⟨1689906537873804581486839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9012834868660291101263141 1689906537873804581486839)
            ·
              refine ⟨2534859806810706872230259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689906537873804581486839 2534859806810706872230259)
              ·
                refine ⟨3802289710216060308345389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2534859806810706872230259 3802289710216060308345389)
                ·
                  refine ⟨1425858641331022615629521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3802289710216060308345389 1425858641331022615629521)
                  ·
                    refine ⟨1069393980998266961722141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1425858641331022615629521 1069393980998266961722141)
                    ·
                      refine ⟨401022742874350110645803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1069393980998266961722141 401022742874350110645803)
                      ·
                        rfl

theorem cell23_780989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_780989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_780989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_780989 prefixEnd_780989 := by exact prefixLift 780989
  have htrace : WordTrace (prefixWord ++ tailWord_780989) baseStart_780989 baseEnd_780989 := by
    simpa [prefixWord, tailWord_780989, baseEnd_780989] using wordTrace_append hprefix tailTrace_780989
  have hstable : (prefixWord ++ tailWord_780989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_780989).length < 2 ^ (prefixWord ++ tailWord_780989).sum := by decide
  have hdescent : baseEnd_780989 < baseStart_780989 := by decide
  rcases family_descends (prefixWord ++ tailWord_780989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781013 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 2, 4]
def baseStart_781013 : Nat := 118140960795 + 781013 * 2 ^ 59
def prefixEnd_781013 : Nat := 4983230072969 + 3 ^ 40 * 781013 * 2
def baseEnd_781013 : Nat := 133678355470019338915231

theorem tailTrace_781013 : CollatzResearch.WordTrace tailWord_781013 prefixEnd_781013 133678355470019338915231 := by
  unfold tailWord_781013
  simp only [CollatzResearch.WordTrace]
  refine ⟨28485884319530762246075693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18990589546353841497383795 28485884319530762246075693)
  ·
    refine ⟨10682206619824035842278385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28485884319530762246075693 10682206619824035842278385)
    ·
      refine ⟨8011654964868026881708789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10682206619824035842278385 8011654964868026881708789)
      ·
        refine ⟨751092652956377520160199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8011654964868026881708789 751092652956377520160199)
        ·
          refine ⟨1126638979434566280240299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751092652956377520160199 1126638979434566280240299)
          ·
            refine ⟨1689958469151849420360449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126638979434566280240299 1689958469151849420360449)
            ·
              refine ⟨1267468851863887065270337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1689958469151849420360449 1267468851863887065270337)
              ·
                refine ⟨950601638897915298952753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267468851863887065270337 950601638897915298952753)
                ·
                  refine ⟨712951229173436474214565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 950601638897915298952753 712951229173436474214565)
                  ·
                    refine ⟨133678355470019338915231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 712951229173436474214565 133678355470019338915231)
                    ·
                      rfl

theorem cell23_781013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_781013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781013 prefixEnd_781013 := by exact prefixLift 781013
  have htrace : WordTrace (prefixWord ++ tailWord_781013) baseStart_781013 baseEnd_781013 := by
    simpa [prefixWord, tailWord_781013, baseEnd_781013] using wordTrace_append hprefix tailTrace_781013
  have hstable : (prefixWord ++ tailWord_781013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781013).length < 2 ^ (prefixWord ++ tailWord_781013).sum := by decide
  have hdescent : baseEnd_781013 < baseStart_781013 := by decide
  rcases family_descends (prefixWord ++ tailWord_781013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781046 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2]
def baseStart_781046 : Nat := 118140960795 + 781046 * 2 ^ 59
def prefixEnd_781046 : Nat := 4983230072969 + 3 ^ 40 * 781046 * 2
def baseEnd_781046 : Nat := 401052011271656387633041

theorem tailTrace_781046 : CollatzResearch.WordTrace tailWord_781046 prefixEnd_781046 401052011271656387633041 := by
  unfold tailWord_781046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1780442995525700555126687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18991391952274139254684661 1780442995525700555126687)
  ·
    refine ⟨2670664493288550832690031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1780442995525700555126687 2670664493288550832690031)
    ·
      refine ⟨4005996739932826249035047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670664493288550832690031 4005996739932826249035047)
      ·
        refine ⟨6008995109899239373552571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005996739932826249035047 6008995109899239373552571)
        ·
          refine ⟨9013492664848859060328857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6008995109899239373552571 9013492664848859060328857)
          ·
            refine ⟨6760119498636644295246643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9013492664848859060328857 6760119498636644295246643)
            ·
              refine ⟨10140179247954966442869965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760119498636644295246643 10140179247954966442869965)
              ·
                refine ⟨3802567217983112416076237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10140179247954966442869965 3802567217983112416076237)
                ·
                  refine ⟨1425962706743667156028589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3802567217983112416076237 1425962706743667156028589)
                  ·
                    refine ⟨534736015028875183510721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425962706743667156028589 534736015028875183510721)
                    ·
                      refine ⟨401052011271656387633041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 534736015028875183510721 401052011271656387633041)
                      ·
                        rfl

theorem cell23_781046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_781046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781046 prefixEnd_781046 := by exact prefixLift 781046
  have htrace : WordTrace (prefixWord ++ tailWord_781046) baseStart_781046 baseEnd_781046 := by
    simpa [prefixWord, tailWord_781046, baseEnd_781046] using wordTrace_append hprefix tailTrace_781046
  have hstable : (prefixWord ++ tailWord_781046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781046).length < 2 ^ (prefixWord ++ tailWord_781046).sum := by decide
  have hdescent : baseEnd_781046 < baseStart_781046 := by decide
  rcases family_descends (prefixWord ++ tailWord_781046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781063 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 1, 3, 2]
def baseStart_781063 : Nat := 118140960795 + 781063 * 2 ^ 59
def prefixEnd_781063 : Nat := 4983230072969 + 3 ^ 40 * 781063 * 2
def baseEnd_781063 : Nat := 401060740442782821120463

theorem tailTrace_781063 : CollatzResearch.WordTrace tailWord_781063 prefixEnd_781063 401060740442782821120463 := by
  unfold tailWord_781063
  simp only [CollatzResearch.WordTrace]
  refine ⟨28487707969349620785395843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18991805312899747190263895 28487707969349620785395843)
  ·
    refine ⟨42731561954024431178093765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28487707969349620785395843 42731561954024431178093765)
    ·
      refine ⟨8012167866379580845892581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42731561954024431178093765 8012167866379580845892581)
      ·
        refine ⟨1502281474946171408604859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8012167866379580845892581 1502281474946171408604859)
        ·
          refine ⟨2253422212419257112907289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1502281474946171408604859 2253422212419257112907289)
          ·
            refine ⟨1690066659314442834680467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2253422212419257112907289 1690066659314442834680467)
            ·
              refine ⟨2535099988971664252020701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690066659314442834680467 2535099988971664252020701)
              ·
                refine ⟨950662495864374094507763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2535099988971664252020701 950662495864374094507763)
                ·
                  refine ⟨1425993743796561141761645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950662495864374094507763 1425993743796561141761645)
                  ·
                    refine ⟨534747653923710428160617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425993743796561141761645 534747653923710428160617)
                    ·
                      refine ⟨401060740442782821120463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 534747653923710428160617 401060740442782821120463)
                      ·
                        rfl

theorem cell23_781063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_781063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781063 prefixEnd_781063 := by exact prefixLift 781063
  have htrace : WordTrace (prefixWord ++ tailWord_781063) baseStart_781063 baseEnd_781063 := by
    simpa [prefixWord, tailWord_781063, baseEnd_781063] using wordTrace_append hprefix tailTrace_781063
  have hstable : (prefixWord ++ tailWord_781063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781063).length < 2 ^ (prefixWord ++ tailWord_781063).sum := by decide
  have hdescent : baseEnd_781063 < baseStart_781063 := by decide
  rcases family_descends (prefixWord ++ tailWord_781063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781112 : List Nat := [2, 1, 2, 1, 3, 2, 1, 3, 1, 7]
def baseStart_781112 : Nat := 118140960795 + 781112 * 2 ^ 59
def prefixEnd_781112 : Nat := 4983230072969 + 3 ^ 40 * 781112 * 2
def baseEnd_781112 : Nat := 133695300331617709802579

theorem tailTrace_781112 : CollatzResearch.WordTrace tailWord_781112 prefixEnd_781112 133695300331617709802579 := by
  unfold tailWord_781112
  simp only [CollatzResearch.WordTrace]
  refine ⟨14244747573086051076964795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18992996764114734769286393 14244747573086051076964795)
  ·
    refine ⟨21367121359629076615447193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14244747573086051076964795 21367121359629076615447193)
    ·
      refine ⟨16025341019721807461585395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21367121359629076615447193 16025341019721807461585395)
      ·
        refine ⟨24038011529582711192378093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16025341019721807461585395 24038011529582711192378093)
        ·
          refine ⟨9014254323593516697141785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24038011529582711192378093 9014254323593516697141785)
          ·
            refine ⟨6760690742695137522856339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9014254323593516697141785 6760690742695137522856339)
            ·
              refine ⟨10141036114042706284284509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6760690742695137522856339 10141036114042706284284509)
              ·
                refine ⟨3802888542766014856606691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10141036114042706284284509 3802888542766014856606691)
                ·
                  refine ⟨5704332814149022284910037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3802888542766014856606691 5704332814149022284910037)
                  ·
                    refine ⟨133695300331617709802579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5704332814149022284910037 133695300331617709802579)
                    ·
                      rfl

theorem cell23_781112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_781112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781112 prefixEnd_781112 := by exact prefixLift 781112
  have htrace : WordTrace (prefixWord ++ tailWord_781112) baseStart_781112 baseEnd_781112 := by
    simpa [prefixWord, tailWord_781112, baseEnd_781112] using wordTrace_append hprefix tailTrace_781112
  have hstable : (prefixWord ++ tailWord_781112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781112).length < 2 ^ (prefixWord ++ tailWord_781112).sum := by decide
  have hdescent : baseEnd_781112 < baseStart_781112 := by decide
  rcases family_descends (prefixWord ++ tailWord_781112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781129 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 2, 5]
def baseStart_781129 : Nat := 118140960795 + 781129 * 2 ^ 59
def prefixEnd_781129 : Nat := 4983230072969 + 3 ^ 40 * 781129 * 2
def baseEnd_781129 : Nat := 133698210055326520965053

theorem tailTrace_781129 : CollatzResearch.WordTrace tailWord_781129 prefixEnd_781129 133698210055326520965053 := by
  unfold tailWord_781129
  simp only [CollatzResearch.WordTrace]
  refine ⟨28490115187110514057298441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18993410124740342704865627 28490115187110514057298441)
  ·
    refine ⟨21367586390332885542973831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28490115187110514057298441 21367586390332885542973831)
    ·
      refine ⟨32051379585499328314460747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21367586390332885542973831 32051379585499328314460747)
      ·
        refine ⟨48077069378248992471691121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32051379585499328314460747 48077069378248992471691121)
        ·
          refine ⟨36057802033686744353768341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48077069378248992471691121 36057802033686744353768341)
          ·
            refine ⟨1690209470329066141582891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36057802033686744353768341 1690209470329066141582891)
            ·
              refine ⟨2535314205493599212374337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690209470329066141582891 2535314205493599212374337)
              ·
                refine ⟨1901485654120199409280753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2535314205493599212374337 1901485654120199409280753)
                ·
                  refine ⟨1426114240590149556960565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1901485654120199409280753 1426114240590149556960565)
                  ·
                    refine ⟨133698210055326520965053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1426114240590149556960565 133698210055326520965053)
                    ·
                      rfl

theorem cell23_781129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_781129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781129 prefixEnd_781129 := by exact prefixLift 781129
  have htrace : WordTrace (prefixWord ++ tailWord_781129) baseStart_781129 baseEnd_781129 := by
    simpa [prefixWord, tailWord_781129, baseEnd_781129] using wordTrace_append hprefix tailTrace_781129
  have hstable : (prefixWord ++ tailWord_781129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781129).length < 2 ^ (prefixWord ++ tailWord_781129).sum := by decide
  have hdescent : baseEnd_781129 < baseStart_781129 := by decide
  rcases family_descends (prefixWord ++ tailWord_781129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781133 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 7]
def baseStart_781133 : Nat := 118140960795 + 781133 * 2 ^ 59
def prefixEnd_781133 : Nat := 4983230072969 + 3 ^ 40 * 781133 * 2
def baseEnd_781133 : Nat := 44566298232066394138349

theorem tailTrace_781133 : CollatzResearch.WordTrace tailWord_781133 prefixEnd_781133 44566298232066394138349 := by
  unfold tailWord_781133
  simp only [CollatzResearch.WordTrace]
  refine ⟨28490261079096022740444053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18993507386064015160296035 28490261079096022740444053)
  ·
    refine ⟨1335480988082626065958315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28490261079096022740444053 1335480988082626065958315)
    ·
      refine ⟨2003221482123939098937473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335480988082626065958315 2003221482123939098937473)
      ·
        refine ⟨1502416111592954324203105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2003221482123939098937473 1502416111592954324203105)
        ·
          refine ⟨1126812083694715743152329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1502416111592954324203105 1126812083694715743152329)
          ·
            refine ⟨845109062771036807364247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1126812083694715743152329 845109062771036807364247)
            ·
              refine ⟨1267663594156555211046371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845109062771036807364247 1267663594156555211046371)
              ·
                refine ⟨1901495391234832816569557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1267663594156555211046371 1901495391234832816569557)
                ·
                  refine ⟨44566298232066394138349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1901495391234832816569557 44566298232066394138349)
                  ·
                    rfl

theorem cell23_781133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_781133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781133 prefixEnd_781133 := by exact prefixLift 781133
  have htrace : WordTrace (prefixWord ++ tailWord_781133) baseStart_781133 baseEnd_781133 := by
    simpa [prefixWord, tailWord_781133, baseEnd_781133] using wordTrace_append hprefix tailTrace_781133
  have hstable : (prefixWord ++ tailWord_781133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781133).length < 2 ^ (prefixWord ++ tailWord_781133).sum := by decide
  have hdescent : baseEnd_781133 < baseStart_781133 := by decide
  rcases family_descends (prefixWord ++ tailWord_781133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781189 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 6]
def baseStart_781189 : Nat := 118140960795 + 781189 * 2 ^ 59
def prefixEnd_781189 : Nat := 4983230072969 + 3 ^ 40 * 781189 * 2
def baseEnd_781189 : Nat := 44569493222805480904987

theorem tailTrace_781189 : CollatzResearch.WordTrace tailWord_781189 prefixEnd_781189 44569493222805480904987 := by
  unfold tailWord_781189
  simp only [CollatzResearch.WordTrace]
  refine ⟨28492303566893144304482621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18994869044595429536321747 28492303566893144304482621)
  ·
    refine ⟨10684613837584929114180983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28492303566893144304482621 10684613837584929114180983)
    ·
      refine ⟨16026920756377393671271475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10684613837584929114180983 16026920756377393671271475)
      ·
        refine ⟨24040381134566090506907213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16026920756377393671271475 24040381134566090506907213)
        ·
          refine ⟨9015142925462283940090205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24040381134566090506907213 9015142925462283940090205)
          ·
            refine ⟨3380678597048356477533827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9015142925462283940090205 3380678597048356477533827)
            ·
              refine ⟨5071017895572534716300741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380678597048356477533827 5071017895572534716300741)
              ·
                refine ⟨950815855419850259306389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5071017895572534716300741 950815855419850259306389)
                ·
                  refine ⟨44569493222805480904987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 950815855419850259306389 44569493222805480904987)
                  ·
                    rfl

theorem cell23_781189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_781189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781189 prefixEnd_781189 := by exact prefixLift 781189
  have htrace : WordTrace (prefixWord ++ tailWord_781189) baseStart_781189 baseEnd_781189 := by
    simpa [prefixWord, tailWord_781189, baseEnd_781189] using wordTrace_append hprefix tailTrace_781189
  have hstable : (prefixWord ++ tailWord_781189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781189).length < 2 ^ (prefixWord ++ tailWord_781189).sum := by decide
  have hdescent : baseEnd_781189 < baseStart_781189 := by decide
  rcases family_descends (prefixWord ++ tailWord_781189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781193 : List Nat := [1, 2, 1, 1, 5, 3, 1, 4, 1, 4]
def baseStart_781193 : Nat := 118140960795 + 781193 * 2 ^ 59
def prefixEnd_781193 : Nat := 4983230072969 + 3 ^ 40 * 781193 * 2
def baseEnd_781193 : Nat := 133709164309289104164955

theorem tailTrace_781193 : CollatzResearch.WordTrace tailWord_781193 prefixEnd_781193 133709164309289104164955 := by
  unfold tailWord_781193
  simp only [CollatzResearch.WordTrace]
  refine ⟨28492449458878652987628233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18994966305919101991752155 28492449458878652987628233)
  ·
    refine ⟨21369337094158989740721175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28492449458878652987628233 21369337094158989740721175)
    ·
      refine ⟨32054005641238484611081763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21369337094158989740721175 32054005641238484611081763)
      ·
        refine ⟨48081008461857726916622645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32054005641238484611081763 48081008461857726916622645)
        ·
          refine ⟨4507594543299161898433373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48081008461857726916622645 4507594543299161898433373)
          ·
            refine ⟨1690347953737185711912515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4507594543299161898433373 1690347953737185711912515)
            ·
              refine ⟨2535521930605778567868773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690347953737185711912515 2535521930605778567868773)
              ·
                refine ⟨475410361988583481475395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2535521930605778567868773 475410361988583481475395)
                ·
                  refine ⟨713115542982875222213093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475410361988583481475395 713115542982875222213093)
                  ·
                    refine ⟨133709164309289104164955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 713115542982875222213093 133709164309289104164955)
                    ·
                      rfl

theorem cell23_781193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 4].length) (baseStart_781193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781193 prefixEnd_781193 := by exact prefixLift 781193
  have htrace : WordTrace (prefixWord ++ tailWord_781193) baseStart_781193 baseEnd_781193 := by
    simpa [prefixWord, tailWord_781193, baseEnd_781193] using wordTrace_append hprefix tailTrace_781193
  have hstable : (prefixWord ++ tailWord_781193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781193).length < 2 ^ (prefixWord ++ tailWord_781193).sum := by decide
  have hdescent : baseEnd_781193 < baseStart_781193 := by decide
  rcases family_descends (prefixWord ++ tailWord_781193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781216 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 5, 1, 3]
def baseStart_781216 : Nat := 118140960795 + 781216 * 2 ^ 59
def prefixEnd_781216 : Nat := 4983230072969 + 3 ^ 40 * 781216 * 2
def baseEnd_781216 : Nat := 401139302982920722507259

theorem tailTrace_781216 : CollatzResearch.WordTrace tailWord_781216 prefixEnd_781216 401139302982920722507259 := by
  unfold tailWord_781216
  simp only [CollatzResearch.WordTrace]
  refine ⟨14246644168897663957857751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18995525558530218610477001 14246644168897663957857751)
  ·
    refine ⟨21369966253346495936786627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14246644168897663957857751 21369966253346495936786627)
    ·
      refine ⟨32054949380019743905179941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21369966253346495936786627 32054949380019743905179941)
      ·
        refine ⟨6010303008753701982221239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32054949380019743905179941 6010303008753701982221239)
        ·
          refine ⟨9015454513130552973331859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6010303008753701982221239 9015454513130552973331859)
          ·
            refine ⟨13523181769695829459997789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9015454513130552973331859 13523181769695829459997789)
            ·
              refine ⟨5071193163635936047499171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13523181769695829459997789 5071193163635936047499171)
              ·
                refine ⟨7606789745453904071248757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071193163635936047499171 7606789745453904071248757)
                ·
                  refine ⟨713136538636303506679571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7606789745453904071248757 713136538636303506679571)
                  ·
                    refine ⟨1069704807954455260019357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 713136538636303506679571 1069704807954455260019357)
                    ·
                      refine ⟨401139302982920722507259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1069704807954455260019357 401139302982920722507259)
                      ·
                        rfl

theorem cell23_781216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_781216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781216 prefixEnd_781216 := by exact prefixLift 781216
  have htrace : WordTrace (prefixWord ++ tailWord_781216) baseStart_781216 baseEnd_781216 := by
    simpa [prefixWord, tailWord_781216, baseEnd_781216] using wordTrace_append hprefix tailTrace_781216
  have hstable : (prefixWord ++ tailWord_781216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781216).length < 2 ^ (prefixWord ++ tailWord_781216).sum := by decide
  have hdescent : baseEnd_781216 < baseStart_781216 := by decide
  rcases family_descends (prefixWord ++ tailWord_781216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781219 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 3, 5]
def baseStart_781219 : Nat := 118140960795 + 781219 * 2 ^ 59
def prefixEnd_781219 : Nat := 4983230072969 + 3 ^ 40 * 781219 * 2
def baseEnd_781219 : Nat := 133713614474961403589915

theorem tailTrace_781219 : CollatzResearch.WordTrace tailWord_781219 prefixEnd_781219 133713614474961403589915 := by
  unfold tailWord_781219
  simp only [CollatzResearch.WordTrace]
  refine ⟨28493397756784459428074711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18995598504522972952049807 28493397756784459428074711)
  ·
    refine ⟨42740096635176689142112067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28493397756784459428074711 42740096635176689142112067)
    ·
      refine ⟨64110144952765033713168101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42740096635176689142112067 64110144952765033713168101)
      ·
        refine ⟨12020652178643443821219019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64110144952765033713168101 12020652178643443821219019)
        ·
          refine ⟨18030978267965165731828529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12020652178643443821219019 18030978267965165731828529)
          ·
            refine ⟨13523233700973874298871397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18030978267965165731828529 13523233700973874298871397)
            ·
              refine ⟨2535606318932601431038387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13523233700973874298871397 2535606318932601431038387)
              ·
                refine ⟨3803409478398902146557581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2535606318932601431038387 3803409478398902146557581)
                ·
                  refine ⟨1426278554399588304959093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3803409478398902146557581 1426278554399588304959093)
                  ·
                    refine ⟨133713614474961403589915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1426278554399588304959093 133713614474961403589915)
                    ·
                      rfl

theorem cell23_781219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 5].length) (baseStart_781219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781219 prefixEnd_781219 := by exact prefixLift 781219
  have htrace : WordTrace (prefixWord ++ tailWord_781219) baseStart_781219 baseEnd_781219 := by
    simpa [prefixWord, tailWord_781219, baseEnd_781219] using wordTrace_append hprefix tailTrace_781219
  have hstable : (prefixWord ++ tailWord_781219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781219).length < 2 ^ (prefixWord ++ tailWord_781219).sum := by decide
  have hdescent : baseEnd_781219 < baseStart_781219 := by decide
  rcases family_descends (prefixWord ++ tailWord_781219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781259 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 5]
def baseStart_781259 : Nat := 118140960795 + 781259 * 2 ^ 59
def prefixEnd_781259 : Nat := 4983230072969 + 3 ^ 40 * 781259 * 2
def baseEnd_781259 : Nat := 401161382651064054269561

theorem tailTrace_781259 : CollatzResearch.WordTrace tailWord_781259 prefixEnd_781259 401161382651064054269561 := by
  unfold tailWord_781259
  simp only [CollatzResearch.WordTrace]
  refine ⟨28494856676639546259530831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18996571117759697506353887 28494856676639546259530831)
  ·
    refine ⟨42742285014959319389296247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28494856676639546259530831 42742285014959319389296247)
    ·
      refine ⟨64113427522438979083944371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42742285014959319389296247 64113427522438979083944371)
      ·
        refine ⟨96170141283658468625916557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64113427522438979083944371 96170141283658468625916557)
        ·
          refine ⟨36063802981371925734718709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96170141283658468625916557 36063802981371925734718709)
          ·
            refine ⟨3380981529503618037629879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36063802981371925734718709 3380981529503618037629879)
            ·
              refine ⟨5071472294255427056444819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3380981529503618037629879 5071472294255427056444819)
              ·
                refine ⟨7607208441383140584667229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5071472294255427056444819 7607208441383140584667229)
                ·
                  refine ⟨2852703165518677719250211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7607208441383140584667229 2852703165518677719250211)
                  ·
                    refine ⟨4279054748278016578875317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2852703165518677719250211 4279054748278016578875317)
                    ·
                      refine ⟨401161382651064054269561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4279054748278016578875317 401161382651064054269561)
                      ·
                        rfl

theorem cell23_781259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 5].length) (baseStart_781259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781259 prefixEnd_781259 := by exact prefixLift 781259
  have htrace : WordTrace (prefixWord ++ tailWord_781259) baseStart_781259 baseEnd_781259 := by
    simpa [prefixWord, tailWord_781259, baseEnd_781259] using wordTrace_append hprefix tailTrace_781259
  have hstable : (prefixWord ++ tailWord_781259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781259).length < 2 ^ (prefixWord ++ tailWord_781259).sum := by decide
  have hdescent : baseEnd_781259 < baseStart_781259 := by decide
  rcases family_descends (prefixWord ++ tailWord_781259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781270 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_781270 : Nat := 118140960795 + 781270 * 2 ^ 59
def prefixEnd_781270 : Nat := 4983230072969 + 3 ^ 40 * 781270 * 2
def baseEnd_781270 : Nat := 133722343646087837077337

theorem tailTrace_781270 : CollatzResearch.WordTrace tailWord_781270 prefixEnd_781270 133722343646087837077337 := by
  unfold tailWord_781270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1780953617474980946136329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 18996838586399796758787509 1780953617474980946136329)
  ·
    refine ⟨1335715213106235709602247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1780953617474980946136329 1335715213106235709602247)
    ·
      refine ⟨2003572819659353564403371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335715213106235709602247 2003572819659353564403371)
      ·
        refine ⟨3005359229489030346605057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003572819659353564403371 3005359229489030346605057)
        ·
          refine ⟨2254019422116772759953793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3005359229489030346605057 2254019422116772759953793)
          ·
            refine ⟨1690514566587579569965345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254019422116772759953793 1690514566587579569965345)
            ·
              refine ⟨1267885924940684677474009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1690514566587579569965345 1267885924940684677474009)
              ·
                refine ⟨950914443705513508105507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267885924940684677474009 950914443705513508105507)
                ·
                  refine ⟨1426371665558270262158261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950914443705513508105507 1426371665558270262158261)
                  ·
                    refine ⟨133722343646087837077337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1426371665558270262158261 133722343646087837077337)
                    ·
                      rfl

theorem cell23_781270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_781270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781270 prefixEnd_781270 := by exact prefixLift 781270
  have htrace : WordTrace (prefixWord ++ tailWord_781270) baseStart_781270 baseEnd_781270 := by
    simpa [prefixWord, tailWord_781270, baseEnd_781270] using wordTrace_append hprefix tailTrace_781270
  have hstable : (prefixWord ++ tailWord_781270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781270).length < 2 ^ (prefixWord ++ tailWord_781270).sum := by decide
  have hdescent : baseEnd_781270 < baseStart_781270 := by decide
  rcases family_descends (prefixWord ++ tailWord_781270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781273 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 4]
def baseStart_781273 : Nat := 118140960795 + 781273 * 2 ^ 59
def prefixEnd_781273 : Nat := 4983230072969 + 3 ^ 40 * 781273 * 2
def baseEnd_781273 : Nat := 401168571380226999494497

theorem tailTrace_781273 : CollatzResearch.WordTrace tailWord_781273 prefixEnd_781273 401168571380226999494497 := by
  unfold tailWord_781273
  simp only [CollatzResearch.WordTrace]
  refine ⟨28495367298588826650540473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18996911532392551100360315 28495367298588826650540473)
  ·
    refine ⟨21371525473941619987905355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28495367298588826650540473 21371525473941619987905355)
    ·
      refine ⟨32057288210912429981858033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21371525473941619987905355 32057288210912429981858033)
      ·
        refine ⟨24042966158184322486393525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32057288210912429981858033 24042966158184322486393525)
        ·
          refine ⟨2254028077329780233099393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24042966158184322486393525 2254028077329780233099393)
          ·
            refine ⟨1690521057997335174824545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254028077329780233099393 1690521057997335174824545)
            ·
              refine ⟨1267890793498001381118409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1690521057997335174824545 1267890793498001381118409)
              ·
                refine ⟨950918095123501035838807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267890793498001381118409 950918095123501035838807)
                ·
                  refine ⟨1426377142685251553758211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 950918095123501035838807 1426377142685251553758211)
                  ·
                    refine ⟨2139565714027877330637317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1426377142685251553758211 2139565714027877330637317)
                    ·
                      refine ⟨401168571380226999494497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2139565714027877330637317 401168571380226999494497)
                      ·
                        rfl

theorem cell23_781273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_781273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781273 prefixEnd_781273 := by exact prefixLift 781273
  have htrace : WordTrace (prefixWord ++ tailWord_781273) baseStart_781273 baseEnd_781273 := by
    simpa [prefixWord, tailWord_781273, baseEnd_781273] using wordTrace_append hprefix tailTrace_781273
  have hstable : (prefixWord ++ tailWord_781273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781273).length < 2 ^ (prefixWord ++ tailWord_781273).sum := by decide
  have hdescent : baseEnd_781273 < baseStart_781273 := by decide
  rcases family_descends (prefixWord ++ tailWord_781273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781301 : List Nat := [1, 3, 5, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_781301 : Nat := 118140960795 + 781301 * 2 ^ 59
def prefixEnd_781301 : Nat := 4983230072969 + 3 ^ 40 * 781301 * 2
def baseEnd_781301 : Nat := 401182948838552889944369

theorem tailTrace_781301 : CollatzResearch.WordTrace tailWord_781301 prefixEnd_781301 401182948838552889944369 := by
  unfold tailWord_781301
  simp only [CollatzResearch.WordTrace]
  refine ⟨28496388542487387432559757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18997592361658258288373171 28496388542487387432559757)
  ·
    refine ⟨10686145703432770287209909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28496388542487387432559757 10686145703432770287209909)
    ·
      refine ⟨1001826159696822214425929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10686145703432770287209909 1001826159696822214425929)
      ·
        refine ⟨751369619772616660819447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1001826159696822214425929 751369619772616660819447)
        ·
          refine ⟨1127054429658924991229171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751369619772616660819447 1127054429658924991229171)
          ·
            refine ⟨1690581644488387486843757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127054429658924991229171 1690581644488387486843757)
            ·
              refine ⟨633968116683145307566409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1690581644488387486843757 633968116683145307566409)
              ·
                refine ⟨475476087512358980674807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633968116683145307566409 475476087512358980674807)
                ·
                  refine ⟨713214131268538471012211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475476087512358980674807 713214131268538471012211)
                  ·
                    refine ⟨1069821196902807706518317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 713214131268538471012211 1069821196902807706518317)
                    ·
                      refine ⟨401182948838552889944369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1069821196902807706518317 401182948838552889944369)
                      ·
                        rfl

theorem cell23_781301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_781301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781301 prefixEnd_781301 := by exact prefixLift 781301
  have htrace : WordTrace (prefixWord ++ tailWord_781301) baseStart_781301 baseEnd_781301 := by
    simpa [prefixWord, tailWord_781301, baseEnd_781301] using wordTrace_append hprefix tailTrace_781301
  have hstable : (prefixWord ++ tailWord_781301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781301).length < 2 ^ (prefixWord ++ tailWord_781301).sum := by decide
  have hdescent : baseEnd_781301 < baseStart_781301 := by decide
  rcases family_descends (prefixWord ++ tailWord_781301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781309 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 2, 7]
def baseStart_781309 : Nat := 118140960795 + 781309 * 2 ^ 59
def prefixEnd_781309 : Nat := 4983230072969 + 3 ^ 40 * 781309 * 2
def baseEnd_781309 : Nat := 133729018894596286214777

theorem tailTrace_781309 : CollatzResearch.WordTrace tailWord_781309 prefixEnd_781309 133729018894596286214777 := by
  unfold tailWord_781309
  simp only [CollatzResearch.WordTrace]
  refine ⟨28496680326458404798850981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18997786884305603199233987 28496680326458404798850981)
  ·
    refine ⟨5343127561210950899784559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28496680326458404798850981 5343127561210950899784559)
    ·
      refine ⟨8014691341816426349676839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5343127561210950899784559 8014691341816426349676839)
      ·
        refine ⟨12022037012724639524515259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8014691341816426349676839 12022037012724639524515259)
        ·
          refine ⟨18033055519086959286772889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12022037012724639524515259 18033055519086959286772889)
          ·
            refine ⟨13524791639315219465079667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18033055519086959286772889 13524791639315219465079667)
            ·
              refine ⟨20287187458972829197619501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13524791639315219465079667 20287187458972829197619501)
              ·
                refine ⟨7607695297114810949107313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20287187458972829197619501 7607695297114810949107313)
                ·
                  refine ⟨5705771472836108211830485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7607695297114810949107313 5705771472836108211830485)
                  ·
                    refine ⟨133729018894596286214777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5705771472836108211830485 133729018894596286214777)
                    ·
                      rfl

theorem cell23_781309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_781309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781309 prefixEnd_781309 := by exact prefixLift 781309
  have htrace : WordTrace (prefixWord ++ tailWord_781309) baseStart_781309 baseEnd_781309 := by
    simpa [prefixWord, tailWord_781309, baseEnd_781309] using wordTrace_append hprefix tailTrace_781309
  have hstable : (prefixWord ++ tailWord_781309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781309).length < 2 ^ (prefixWord ++ tailWord_781309).sum := by decide
  have hdescent : baseEnd_781309 < baseStart_781309 := by decide
  rcases family_descends (prefixWord ++ tailWord_781309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781376 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 4]
def baseStart_781376 : Nat := 118140960795 + 781376 * 2 ^ 59
def prefixEnd_781376 : Nat := 4983230072969 + 3 ^ 40 * 781376 * 2
def baseEnd_781376 : Nat := 401221459887640096506523

theorem tailTrace_781376 : CollatzResearch.WordTrace tailWord_781376 prefixEnd_781376 401221459887640096506523 := by
  unfold tailWord_781376
  simp only [CollatzResearch.WordTrace]
  refine ⟨14249562008607837620769991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18999416011477116827693321 14249562008607837620769991)
  ·
    refine ⟨21374343012911756431154987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14249562008607837620769991 21374343012911756431154987)
    ·
      refine ⟨32061514519367634646732481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21374343012911756431154987 32061514519367634646732481)
      ·
        refine ⟨24046135889525725985049361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32061514519367634646732481 24046135889525725985049361)
        ·
          refine ⟨18034601917144294488787021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24046135889525725985049361 18034601917144294488787021)
          ·
            refine ⟨6762975718929110433295133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18034601917144294488787021 6762975718929110433295133)
            ·
              refine ⟨2536115894598416412485675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6762975718929110433295133 2536115894598416412485675)
              ·
                refine ⟨3804173841897624618728513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2536115894598416412485675 3804173841897624618728513)
                ·
                  refine ⟨2853130381423218464046385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3804173841897624618728513 2853130381423218464046385)
                  ·
                    refine ⟨2139847786067413848034789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2853130381423218464046385 2139847786067413848034789)
                    ·
                      refine ⟨401221459887640096506523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2139847786067413848034789 401221459887640096506523)
                      ·
                        rfl

theorem cell23_781376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_781376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781376 prefixEnd_781376 := by exact prefixLift 781376
  have htrace : WordTrace (prefixWord ++ tailWord_781376) baseStart_781376 baseEnd_781376 := by
    simpa [prefixWord, tailWord_781376, baseEnd_781376] using wordTrace_append hprefix tailTrace_781376
  have hstable : (prefixWord ++ tailWord_781376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781376).length < 2 ^ (prefixWord ++ tailWord_781376).sum := by decide
  have hdescent : baseEnd_781376 < baseStart_781376 := by decide
  rcases family_descends (prefixWord ++ tailWord_781376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781426 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_781426 : Nat := 118140960795 + 781426 * 2 ^ 59
def prefixEnd_781426 : Nat := 4983230072969 + 3 ^ 40 * 781426 * 2
def baseEnd_781426 : Nat := 401247133920364900881293

theorem tailTrace_781426 : CollatzResearch.WordTrace tailWord_781426 prefixEnd_781426 401247133920364900881293 := by
  unfold tailWord_781426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7125236916758633445215033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19000631778023022520573421 7125236916758633445215033)
  ·
    refine ⟨5343927687568975083911275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7125236916758633445215033 5343927687568975083911275)
    ·
      refine ⟨8015891531353462625866913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5343927687568975083911275 8015891531353462625866913)
      ·
        refine ⟨6011918648515096969400185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8015891531353462625866913 6011918648515096969400185)
        ·
          refine ⟨4508938986386322727050139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6011918648515096969400185 4508938986386322727050139)
          ·
            refine ⟨6763408479579484090575209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508938986386322727050139 6763408479579484090575209)
            ·
              refine ⟨5072556359684613067931407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6763408479579484090575209 5072556359684613067931407)
              ·
                refine ⟨7608834539526919601897111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072556359684613067931407 7608834539526919601897111)
                ·
                  refine ⟨11413251809290379402845667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7608834539526919601897111 11413251809290379402845667)
                  ·
                    refine ⟨17119877713935569104268501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11413251809290379402845667 17119877713935569104268501)
                    ·
                      refine ⟨401247133920364900881293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17119877713935569104268501 401247133920364900881293)
                      ·
                        rfl

theorem cell23_781426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_781426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781426 prefixEnd_781426 := by exact prefixLift 781426
  have htrace : WordTrace (prefixWord ++ tailWord_781426) baseStart_781426 baseEnd_781426 := by
    simpa [prefixWord, tailWord_781426, baseEnd_781426] using wordTrace_append hprefix tailTrace_781426
  have hstable : (prefixWord ++ tailWord_781426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781426).length < 2 ^ (prefixWord ++ tailWord_781426).sum := by decide
  have hdescent : baseEnd_781426 < baseStart_781426 := by decide
  rcases family_descends (prefixWord ++ tailWord_781426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781436 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_781436 : Nat := 118140960795 + 781436 * 2 ^ 59
def prefixEnd_781436 : Nat := 4983230072969 + 3 ^ 40 * 781436 * 2
def baseEnd_781436 : Nat := 401252268726909861756247

theorem tailTrace_781436 : CollatzResearch.WordTrace tailWord_781436 prefixEnd_781436 401252268726909861756247 := by
  unfold tailWord_781436
  simp only [CollatzResearch.WordTrace]
  refine ⟨14250656198499152744362081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19000874931332203659149441 14250656198499152744362081)
  ·
    refine ⟨10687992148874364558271561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14250656198499152744362081 10687992148874364558271561)
    ·
      refine ⟨8015994111655773418703671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10687992148874364558271561 8015994111655773418703671)
      ·
        refine ⟨12023991167483660128055507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8015994111655773418703671 12023991167483660128055507)
        ·
          refine ⟨18035986751225490192083261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12023991167483660128055507 18035986751225490192083261)
          ·
            refine ⟨6763495031709558822031223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18035986751225490192083261 6763495031709558822031223)
            ·
              refine ⟨10145242547564338233046835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6763495031709558822031223 10145242547564338233046835)
              ·
                refine ⟨15217863821346507349570253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10145242547564338233046835 15217863821346507349570253)
                ·
                  refine ⟨5706698933004940256088845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15217863821346507349570253 5706698933004940256088845)
                  ·
                    refine ⟨2140012099876852596033317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5706698933004940256088845 2140012099876852596033317)
                    ·
                      refine ⟨401252268726909861756247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2140012099876852596033317 401252268726909861756247)
                      ·
                        rfl

theorem cell23_781436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_781436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781436 prefixEnd_781436 := by exact prefixLift 781436
  have htrace : WordTrace (prefixWord ++ tailWord_781436) baseStart_781436 baseEnd_781436 := by
    simpa [prefixWord, tailWord_781436, baseEnd_781436] using wordTrace_append hprefix tailTrace_781436
  have hstable : (prefixWord ++ tailWord_781436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781436).length < 2 ^ (prefixWord ++ tailWord_781436).sum := by decide
  have hdescent : baseEnd_781436 < baseStart_781436 := by decide
  rcases family_descends (prefixWord ++ tailWord_781436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781470 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_781470 : Nat := 118140960795 + 781470 * 2 ^ 59
def prefixEnd_781470 : Nat := 4983230072969 + 3 ^ 40 * 781470 * 2
def baseEnd_781470 : Nat := 401269727069162728731091

theorem tailTrace_781470 : CollatzResearch.WordTrace tailWord_781470 prefixEnd_781470 401269727069162728731091 := by
  unfold tailWord_781470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562819059859391161932733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19001701652583419530307909 3562819059859391161932733)
  ·
    refine ⟨1336057147447271685724775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3562819059859391161932733 1336057147447271685724775)
    ·
      refine ⟨2004085721170907528587163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336057147447271685724775 2004085721170907528587163)
      ·
        refine ⟨3006128581756361292880745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004085721170907528587163 3006128581756361292880745)
        ·
          refine ⟨2254596436317270969660559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3006128581756361292880745 2254596436317270969660559)
          ·
            refine ⟨3381894654475906454490839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2254596436317270969660559 3381894654475906454490839)
            ·
              refine ⟨5072841981713859681736259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381894654475906454490839 5072841981713859681736259)
              ·
                refine ⟨7609262972570789522604389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5072841981713859681736259 7609262972570789522604389)
                ·
                  refine ⟨1426736807357023035488323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7609262972570789522604389 1426736807357023035488323)
                  ·
                    refine ⟨2140105211035534553232485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1426736807357023035488323 2140105211035534553232485)
                    ·
                      refine ⟨401269727069162728731091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2140105211035534553232485 401269727069162728731091)
                      ·
                        rfl

theorem cell23_781470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_781470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781470 prefixEnd_781470 := by exact prefixLift 781470
  have htrace : WordTrace (prefixWord ++ tailWord_781470) baseStart_781470 baseEnd_781470 := by
    simpa [prefixWord, tailWord_781470, baseEnd_781470] using wordTrace_append hprefix tailTrace_781470
  have hstable : (prefixWord ++ tailWord_781470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781470).length < 2 ^ (prefixWord ++ tailWord_781470).sum := by decide
  have hdescent : baseEnd_781470 < baseStart_781470 := by decide
  rcases family_descends (prefixWord ++ tailWord_781470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781513 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 5, 5, 2]
def baseStart_781513 : Nat := 118140960795 + 781513 * 2 ^ 59
def prefixEnd_781513 : Nat := 4983230072969 + 3 ^ 40 * 781513 * 2
def baseEnd_781513 : Nat := 401291806737306060493393

theorem tailTrace_781513 : CollatzResearch.WordTrace tailWord_781513 prefixEnd_781513 401291806737306060493393 := by
  unfold tailWord_781513
  simp only [CollatzResearch.WordTrace]
  refine ⟨28504120817719347639277193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19002747211812898426184795 28504120817719347639277193)
  ·
    refine ⟨21378090613289510729457895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28504120817719347639277193 21378090613289510729457895)
    ·
      refine ⟨32067135919934266094186843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21378090613289510729457895 32067135919934266094186843)
      ·
        refine ⟨48100703879901399141280265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32067135919934266094186843 48100703879901399141280265)
        ·
          refine ⟨36075527909926049355960199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48100703879901399141280265 36075527909926049355960199)
          ·
            refine ⟨54113291864889074033940299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36075527909926049355960199 54113291864889074033940299)
            ·
              refine ⟨81169937797333611050910449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54113291864889074033940299 81169937797333611050910449)
              ·
                refine ⟨60877453348000208288182837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81169937797333611050910449 60877453348000208288182837)
                ·
                  refine ⟨5707261251375019527017141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60877453348000208288182837 5707261251375019527017141)
                  ·
                    refine ⟨535055742316408080657857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5707261251375019527017141 535055742316408080657857)
                    ·
                      refine ⟨401291806737306060493393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535055742316408080657857 401291806737306060493393)
                      ·
                        rfl

theorem cell23_781513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 5, 2].length) (baseStart_781513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781513 prefixEnd_781513 := by exact prefixLift 781513
  have htrace : WordTrace (prefixWord ++ tailWord_781513) baseStart_781513 baseEnd_781513 := by
    simpa [prefixWord, tailWord_781513, baseEnd_781513] using wordTrace_append hprefix tailTrace_781513
  have hstable : (prefixWord ++ tailWord_781513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781513).length < 2 ^ (prefixWord ++ tailWord_781513).sum := by decide
  have hdescent : baseEnd_781513 < baseStart_781513 := by decide
  rcases family_descends (prefixWord ++ tailWord_781513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781553 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 6, 4]
def baseStart_781553 : Nat := 118140960795 + 781553 * 2 ^ 59
def prefixEnd_781553 : Nat := 4983230072969 + 3 ^ 40 * 781553 * 2
def baseEnd_781553 : Nat := 133770781987828634664403

theorem tailTrace_781553 : CollatzResearch.WordTrace tailWord_781553 prefixEnd_781553 133770781987828634664403 := by
  unfold tailWord_781553
  simp only [CollatzResearch.WordTrace]
  refine ⟨28505579737574434470733313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19003719825049622980488875 28505579737574434470733313)
  ·
    refine ⟨21379184803180825853049985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28505579737574434470733313 21379184803180825853049985)
    ·
      refine ⟨16034388602385619389787489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21379184803180825853049985 16034388602385619389787489)
      ·
        refine ⟨12025791451789214542340617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16034388602385619389787489 12025791451789214542340617)
        ·
          refine ⟨9019343588841910906755463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12025791451789214542340617 9019343588841910906755463)
          ·
            refine ⟨13529015383262866360133195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9019343588841910906755463 13529015383262866360133195)
            ·
              refine ⟨20293523074894299540199793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13529015383262866360133195 20293523074894299540199793)
              ·
                refine ⟨15220142306170724655149845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20293523074894299540199793 15220142306170724655149845)
                ·
                  refine ⟨713444170601752718210149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15220142306170724655149845 713444170601752718210149)
                  ·
                    refine ⟨133770781987828634664403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 713444170601752718210149 133770781987828634664403)
                    ·
                      rfl

theorem cell23_781553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_781553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781553 prefixEnd_781553 := by exact prefixLift 781553
  have htrace : WordTrace (prefixWord ++ tailWord_781553) baseStart_781553 baseEnd_781553 := by
    simpa [prefixWord, tailWord_781553, baseEnd_781553] using wordTrace_append hprefix tailTrace_781553
  have hstable : (prefixWord ++ tailWord_781553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781553).length < 2 ^ (prefixWord ++ tailWord_781553).sum := by decide
  have hdescent : baseEnd_781553 < baseStart_781553 := by decide
  rcases family_descends (prefixWord ++ tailWord_781553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781564 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_781564 : Nat := 118140960795 + 781564 * 2 ^ 59
def prefixEnd_781564 : Nat := 4983230072969 + 3 ^ 40 * 781564 * 2
def baseEnd_781564 : Nat := 401317994250685360955659

theorem tailTrace_781564 : CollatzResearch.WordTrace tailWord_781564 prefixEnd_781564 401317994250685360955659 := by
  unfold tailWord_781564
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252990470267291674691873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19003987293689722232922497 14252990470267291674691873)
  ·
    refine ⟨10689742852700468756018905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14252990470267291674691873 10689742852700468756018905)
    ·
      refine ⟨8017307139525351567014179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10689742852700468756018905 8017307139525351567014179)
      ·
        refine ⟨12025960709288027350521269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8017307139525351567014179 12025960709288027350521269)
        ·
          refine ⟨1127433816495752564111369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12025960709288027350521269 1127433816495752564111369)
          ·
            refine ⟨845575362371814423083527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127433816495752564111369 845575362371814423083527)
            ·
              refine ⟨1268363043557721634625291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845575362371814423083527 1268363043557721634625291)
              ·
                refine ⟨1902544565336582451937937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268363043557721634625291 1902544565336582451937937)
                ·
                  refine ⟨1426908424002436838953453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1902544565336582451937937 1426908424002436838953453)
                  ·
                    refine ⟨535090659000913814607545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1426908424002436838953453 535090659000913814607545)
                    ·
                      refine ⟨401317994250685360955659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535090659000913814607545 401317994250685360955659)
                      ·
                        rfl

theorem cell23_781564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_781564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781564 prefixEnd_781564 := by exact prefixLift 781564
  have htrace : WordTrace (prefixWord ++ tailWord_781564) baseStart_781564 baseEnd_781564 := by
    simpa [prefixWord, tailWord_781564, baseEnd_781564] using wordTrace_append hprefix tailTrace_781564
  have hstable : (prefixWord ++ tailWord_781564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781564).length < 2 ^ (prefixWord ++ tailWord_781564).sum := by decide
  have hdescent : baseEnd_781564 < baseStart_781564 := by decide
  rcases family_descends (prefixWord ++ tailWord_781564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781573 : List Nat := [1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_781573 : Nat := 118140960795 + 781573 * 2 ^ 59
def prefixEnd_781573 : Nat := 4983230072969 + 3 ^ 40 * 781573 * 2
def baseEnd_781573 : Nat := 401322615576575825743117

theorem tailTrace_781573 : CollatzResearch.WordTrace tailWord_781573 prefixEnd_781573 401322615576575825743117 := by
  unfold tailWord_781573
  simp only [CollatzResearch.WordTrace]
  refine ⟨28506309197501977886461373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19004206131667985257640915 28506309197501977886461373)
  ·
    refine ⟨10689865949063241707423015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28506309197501977886461373 10689865949063241707423015)
    ·
      refine ⟨16034798923594862561134523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10689865949063241707423015 16034798923594862561134523)
      ·
        refine ⟨24052198385392293841701785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16034798923594862561134523 24052198385392293841701785)
        ·
          refine ⟨18039148789044220381276339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24052198385392293841701785 18039148789044220381276339)
          ·
            refine ⟨27058723183566330571914509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18039148789044220381276339 27058723183566330571914509)
            ·
              refine ⟨10147021193837373964467941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27058723183566330571914509 10147021193837373964467941)
              ·
                refine ⟨1902566473844507618337739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10147021193837373964467941 1902566473844507618337739)
                ·
                  refine ⟨2853849710766761427506609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1902566473844507618337739 2853849710766761427506609)
                  ·
                    refine ⟨2140387283075071070629957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2853849710766761427506609 2140387283075071070629957)
                    ·
                      refine ⟨401322615576575825743117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2140387283075071070629957 401322615576575825743117)
                      ·
                        rfl

theorem cell23_781573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_781573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781573 prefixEnd_781573 := by exact prefixLift 781573
  have htrace : WordTrace (prefixWord ++ tailWord_781573) baseStart_781573 baseEnd_781573 := by
    simpa [prefixWord, tailWord_781573, baseEnd_781573] using wordTrace_append hprefix tailTrace_781573
  have hstable : (prefixWord ++ tailWord_781573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781573).length < 2 ^ (prefixWord ++ tailWord_781573).sum := by decide
  have hdescent : baseEnd_781573 < baseStart_781573 := by decide
  rcases family_descends (prefixWord ++ tailWord_781573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781594 : List Nat := [3, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2]
def baseStart_781594 : Nat := 118140960795 + 781594 * 2 ^ 59
def prefixEnd_781594 : Nat := 4983230072969 + 3 ^ 40 * 781594 * 2
def baseEnd_781594 : Nat := 401333398670320243580521

theorem tailTrace_781594 : CollatzResearch.WordTrace tailWord_781594 prefixEnd_781594 401333398670320243580521 := by
  unfold tailWord_781594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126768782606474618243959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19004716753617265648650557 7126768782606474618243959)
  ·
    refine ⟨10690153173909711927365939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7126768782606474618243959 10690153173909711927365939)
    ·
      refine ⟨16035229760864567891048909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10690153173909711927365939 16035229760864567891048909)
      ·
        refine ⟨6013211160324212959143341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16035229760864567891048909 6013211160324212959143341)
        ·
          refine ⟨2254954185121579859678753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6013211160324212959143341 2254954185121579859678753)
          ·
            refine ⟨1691215638841184894759065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2254954185121579859678753 1691215638841184894759065)
            ·
              refine ⟨1268411729130888671069299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691215638841184894759065 1268411729130888671069299)
              ·
                refine ⟨1902617593696333006603949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268411729130888671069299 1902617593696333006603949)
                ·
                  refine ⟨713481597636124877476481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1902617593696333006603949 713481597636124877476481)
                  ·
                    refine ⟨535111198227093658107361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 713481597636124877476481 535111198227093658107361)
                    ·
                      refine ⟨401333398670320243580521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535111198227093658107361 401333398670320243580521)
                      ·
                        rfl

theorem cell23_781594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_781594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781594 prefixEnd_781594 := by exact prefixLift 781594
  have htrace : WordTrace (prefixWord ++ tailWord_781594) baseStart_781594 baseEnd_781594 := by
    simpa [prefixWord, tailWord_781594, baseEnd_781594] using wordTrace_append hprefix tailTrace_781594
  have hstable : (prefixWord ++ tailWord_781594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781594).length < 2 ^ (prefixWord ++ tailWord_781594).sum := by decide
  have hdescent : baseEnd_781594 < baseStart_781594 := by decide
  rcases family_descends (prefixWord ++ tailWord_781594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781645 : List Nat := [1, 6, 1, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_781645 : Nat := 118140960795 + 781645 * 2 ^ 59
def prefixEnd_781645 : Nat := 4983230072969 + 3 ^ 40 * 781645 * 2
def baseEnd_781645 : Nat := 401359586183699544042787

theorem tailTrace_781645 : CollatzResearch.WordTrace tailWord_781645 prefixEnd_781645 401359586183699544042787 := by
  unfold tailWord_781645
  simp only [CollatzResearch.WordTrace]
  refine ⟨28508935253241134183082389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19005956835494089455388259 28508935253241134183082389)
  ·
    refine ⟨1336356339995678164831987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28508935253241134183082389 1336356339995678164831987)
    ·
      refine ⟨2004534509993517247247981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336356339995678164831987 2004534509993517247247981)
      ·
        refine ⟨751700441247568967717993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2004534509993517247247981 751700441247568967717993)
        ·
          refine ⟨563775330935676725788495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751700441247568967717993 563775330935676725788495)
          ·
            refine ⟨845662996403515088682743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563775330935676725788495 845662996403515088682743)
            ·
              refine ⟨1268494494605272633024115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845662996403515088682743 1268494494605272633024115)
              ·
                refine ⟨1902741741907908949536173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268494494605272633024115 1902741741907908949536173)
                ·
                  refine ⟨713528153215465856076065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1902741741907908949536173 713528153215465856076065)
                  ·
                    refine ⟨535146114911599392057049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 713528153215465856076065 535146114911599392057049)
                    ·
                      refine ⟨401359586183699544042787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535146114911599392057049 401359586183699544042787)
                      ·
                        rfl

theorem cell23_781645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_781645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781645 prefixEnd_781645 := by exact prefixLift 781645
  have htrace : WordTrace (prefixWord ++ tailWord_781645) baseStart_781645 baseEnd_781645 := by
    simpa [prefixWord, tailWord_781645, baseEnd_781645] using wordTrace_append hprefix tailTrace_781645
  have hstable : (prefixWord ++ tailWord_781645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781645).length < 2 ^ (prefixWord ++ tailWord_781645).sum := by decide
  have hdescent : baseEnd_781645 < baseStart_781645 := by decide
  rcases family_descends (prefixWord ++ tailWord_781645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781663 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_781663 : Nat := 118140960795 + 781663 * 2 ^ 59
def prefixEnd_781663 : Nat := 4983230072969 + 3 ^ 40 * 781663 * 2
def baseEnd_781663 : Nat := 401368828835480473617703

theorem tailTrace_781663 : CollatzResearch.WordTrace tailWord_781663 prefixEnd_781663 401368828835480473617703 := by
  unfold tailWord_781663
  simp only [CollatzResearch.WordTrace]
  refine ⟨28509591767175923257237643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19006394511450615504825095 28509591767175923257237643)
  ·
    refine ⟨42764387650763884885856465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28509591767175923257237643 42764387650763884885856465)
    ·
      refine ⟨32073290738072913664392349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42764387650763884885856465 32073290738072913664392349)
      ·
        refine ⟨12027484026777342624147131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32073290738072913664392349 12027484026777342624147131)
        ·
          refine ⟨18041226040166013936220697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12027484026777342624147131 18041226040166013936220697)
          ·
            refine ⟨13530919530124510452165523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18041226040166013936220697 13530919530124510452165523)
            ·
              refine ⟨20296379295186765678248285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13530919530124510452165523 20296379295186765678248285)
              ·
                refine ⟨7611142235695037129343107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20296379295186765678248285 7611142235695037129343107)
                ·
                  refine ⟨11416713353542555694014661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7611142235695037129343107 11416713353542555694014661)
                  ·
                    refine ⟨2140633753789229192627749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11416713353542555694014661 2140633753789229192627749)
                    ·
                      refine ⟨401368828835480473617703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2140633753789229192627749 401368828835480473617703)
                      ·
                        rfl

theorem cell23_781663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_781663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781663 prefixEnd_781663 := by exact prefixLift 781663
  have htrace : WordTrace (prefixWord ++ tailWord_781663) baseStart_781663 baseEnd_781663 := by
    simpa [prefixWord, tailWord_781663, baseEnd_781663] using wordTrace_append hprefix tailTrace_781663
  have hstable : (prefixWord ++ tailWord_781663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781663).length < 2 ^ (prefixWord ++ tailWord_781663).sum := by decide
  have hdescent : baseEnd_781663 < baseStart_781663 := by decide
  rcases family_descends (prefixWord ++ tailWord_781663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781671 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_781671 : Nat := 118140960795 + 781671 * 2 ^ 59
def prefixEnd_781671 : Nat := 4983230072969 + 3 ^ 40 * 781671 * 2
def baseEnd_781671 : Nat := 401372936680716442317667

theorem tailTrace_781671 : CollatzResearch.WordTrace tailWord_781671 prefixEnd_781671 401372936680716442317667 := by
  unfold tailWord_781671
  simp only [CollatzResearch.WordTrace]
  refine ⟨28509883551146940623528867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19006589034097960415685911 28509883551146940623528867)
  ·
    refine ⟨42764825326720410935293301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28509883551146940623528867 42764825326720410935293301)
    ·
      refine ⟨4009202374380038525183747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42764825326720410935293301 4009202374380038525183747)
      ·
        refine ⟨6013803561570057787775621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4009202374380038525183747 6013803561570057787775621)
        ·
          refine ⟨1127588167794385835207929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6013803561570057787775621 1127588167794385835207929)
          ·
            refine ⟨845691125845789376405947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127588167794385835207929 845691125845789376405947)
            ·
              refine ⟨1268536688768684064608921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845691125845789376405947 1268536688768684064608921)
              ·
                refine ⟨951402516576513048456691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268536688768684064608921 951402516576513048456691)
                ·
                  refine ⟨1427103774864769572685037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951402516576513048456691 1427103774864769572685037)
                  ·
                    refine ⟨535163915574288589756889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1427103774864769572685037 535163915574288589756889)
                    ·
                      refine ⟨401372936680716442317667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535163915574288589756889 401372936680716442317667)
                      ·
                        rfl

theorem cell23_781671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_781671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781671 prefixEnd_781671 := by exact prefixLift 781671
  have htrace : WordTrace (prefixWord ++ tailWord_781671) baseStart_781671 baseEnd_781671 := by
    simpa [prefixWord, tailWord_781671, baseEnd_781671] using wordTrace_append hprefix tailTrace_781671
  have hstable : (prefixWord ++ tailWord_781671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781671).length < 2 ^ (prefixWord ++ tailWord_781671).sum := by decide
  have hdescent : baseEnd_781671 < baseStart_781671 := by decide
  rcases family_descends (prefixWord ++ tailWord_781671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781714 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_781714 : Nat := 118140960795 + 781714 * 2 ^ 59
def prefixEnd_781714 : Nat := 4983230072969 + 3 ^ 40 * 781714 * 2
def baseEnd_781714 : Nat := 401395016348859774079969

theorem tailTrace_781714 : CollatzResearch.WordTrace tailWord_781714 prefixEnd_781714 401395016348859774079969 := by
  unfold tailWord_781714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7127862972497789741836049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19007634593327439311562797 7127862972497789741836049)
  ·
    refine ⟨5345897229373342306377037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7127862972497789741836049 5345897229373342306377037)
    ·
      refine ⟨2004711461015003364891389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5345897229373342306377037 2004711461015003364891389)
      ·
        refine ⟨751766797880626261834271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2004711461015003364891389 751766797880626261834271)
        ·
          refine ⟨1127650196820939392751407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751766797880626261834271 1127650196820939392751407)
          ·
            refine ⟨1691475295231409089127111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127650196820939392751407 1691475295231409089127111)
            ·
              refine ⟨2537212942847113633690667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691475295231409089127111 2537212942847113633690667)
              ·
                refine ⟨3805819414270670450536001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2537212942847113633690667 3805819414270670450536001)
                ·
                  refine ⟨2854364560703002837902001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3805819414270670450536001 2854364560703002837902001)
                  ·
                    refine ⟨2140773420527252128426501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2854364560703002837902001 2140773420527252128426501)
                    ·
                      refine ⟨401395016348859774079969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2140773420527252128426501 401395016348859774079969)
                      ·
                        rfl

theorem cell23_781714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_781714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781714 prefixEnd_781714 := by exact prefixLift 781714
  have htrace : WordTrace (prefixWord ++ tailWord_781714) baseStart_781714 baseEnd_781714 := by
    simpa [prefixWord, tailWord_781714, baseEnd_781714] using wordTrace_append hprefix tailTrace_781714
  have hstable : (prefixWord ++ tailWord_781714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781714).length < 2 ^ (prefixWord ++ tailWord_781714).sum := by decide
  have hdescent : baseEnd_781714 < baseStart_781714 := by decide
  rcases family_descends (prefixWord ++ tailWord_781714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781733 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 1, 10]
def baseStart_781733 : Nat := 118140960795 + 781733 * 2 ^ 59
def prefixEnd_781733 : Nat := 4983230072969 + 3 ^ 40 * 781733 * 2
def baseEnd_781733 : Nat := 133801590827098399914127

theorem tailTrace_781733 : CollatzResearch.WordTrace tailWord_781733 prefixEnd_781733 133801590827098399914127 := by
  unfold tailWord_781733
  simp only [CollatzResearch.WordTrace]
  refine ⟨28512144876922325212285853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19008096584614883474857235 28512144876922325212285853)
  ·
    refine ⟨10692054328845871954607195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28512144876922325212285853 10692054328845871954607195)
    ·
      refine ⟨16038081493268807931910793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10692054328845871954607195 16038081493268807931910793)
      ·
        refine ⟨12028561119951605948933095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16038081493268807931910793 12028561119951605948933095)
        ·
          refine ⟨18042841679927408923399643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12028561119951605948933095 18042841679927408923399643)
          ·
            refine ⟨27064262519891113385099465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18042841679927408923399643 27064262519891113385099465)
            ·
              refine ⟨20298196889918335038824599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27064262519891113385099465 20298196889918335038824599)
              ·
                refine ⟨30447295334877502558236899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20298196889918335038824599 30447295334877502558236899)
                ·
                  refine ⟨45670943002316253837355349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30447295334877502558236899 45670943002316253837355349)
                  ·
                    refine ⟨133801590827098399914127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 45670943002316253837355349 133801590827098399914127)
                    ·
                      rfl

theorem cell23_781733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_781733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781733 prefixEnd_781733 := by exact prefixLift 781733
  have htrace : WordTrace (prefixWord ++ tailWord_781733) baseStart_781733 baseEnd_781733 := by
    simpa [prefixWord, tailWord_781733, baseEnd_781733] using wordTrace_append hprefix tailTrace_781733
  have hstable : (prefixWord ++ tailWord_781733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781733).length < 2 ^ (prefixWord ++ tailWord_781733).sum := by decide
  have hdescent : baseEnd_781733 < baseStart_781733 := by decide
  rcases family_descends (prefixWord ++ tailWord_781733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781757 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_781757 : Nat := 118140960795 + 781757 * 2 ^ 59
def prefixEnd_781757 : Nat := 4983230072969 + 3 ^ 40 * 781757 * 2
def baseEnd_781757 : Nat := 401417096017003105842271

theorem tailTrace_781757 : CollatzResearch.WordTrace tailWord_781757 prefixEnd_781757 401417096017003105842271 := by
  unfold tailWord_781757
  simp only [CollatzResearch.WordTrace]
  refine ⟨28513020228835377311159525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19008680152556918207439683 28513020228835377311159525)
  ·
    refine ⟨5346191292906633245842411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28513020228835377311159525 5346191292906633245842411)
    ·
      refine ⟨8019286939359949868763617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5346191292906633245842411 8019286939359949868763617)
      ·
        refine ⟨6014465204519962401572713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8019286939359949868763617 6014465204519962401572713)
        ·
          refine ⟨4510848903389971801179535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6014465204519962401572713 4510848903389971801179535)
          ·
            refine ⟨6766273355084957701769303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4510848903389971801179535 6766273355084957701769303)
            ·
              refine ⟨10149410032627436552653955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6766273355084957701769303 10149410032627436552653955)
              ·
                refine ⟨15224115048941154828980933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10149410032627436552653955 15224115048941154828980933)
                ·
                  refine ⟨2854521571676466530433925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15224115048941154828980933 2854521571676466530433925)
                  ·
                    refine ⟨535222794689337474456361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2854521571676466530433925 535222794689337474456361)
                    ·
                      refine ⟨401417096017003105842271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535222794689337474456361 401417096017003105842271)
                      ·
                        rfl

theorem cell23_781757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_781757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781757 prefixEnd_781757 := by exact prefixLift 781757
  have htrace : WordTrace (prefixWord ++ tailWord_781757) baseStart_781757 baseEnd_781757 := by
    simpa [prefixWord, tailWord_781757, baseEnd_781757] using wordTrace_append hprefix tailTrace_781757
  have hstable : (prefixWord ++ tailWord_781757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781757).length < 2 ^ (prefixWord ++ tailWord_781757).sum := by decide
  have hdescent : baseEnd_781757 < baseStart_781757 := by decide
  rcases family_descends (prefixWord ++ tailWord_781757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781767 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 3, 4]
def baseStart_781767 : Nat := 118140960795 + 781767 * 2 ^ 59
def prefixEnd_781767 : Nat := 4983230072969 + 3 ^ 40 * 781767 * 2
def baseEnd_781767 : Nat := 133807410274516022239075

theorem tailTrace_781767 : CollatzResearch.WordTrace tailWord_781767 prefixEnd_781767 133807410274516022239075 := by
  unfold tailWord_781767
  simp only [CollatzResearch.WordTrace]
  refine ⟨28513384958799149019023555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19008923305866099346015703 28513384958799149019023555)
  ·
    refine ⟨42770077438198723528535333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28513384958799149019023555 42770077438198723528535333)
    ·
      refine ⟨8019389519662260661600375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42770077438198723528535333 8019389519662260661600375)
      ·
        refine ⟨12029084279493390992400563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8019389519662260661600375 12029084279493390992400563)
        ·
          refine ⟨18043626419240086488600845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12029084279493390992400563 18043626419240086488600845)
          ·
            refine ⟨6766359907215032433225317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18043626419240086488600845 6766359907215032433225317)
            ·
              refine ⟨1268692482602818581229747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6766359907215032433225317 1268692482602818581229747)
              ·
                refine ⟨1903038723904227871844621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268692482602818581229747 1903038723904227871844621)
                ·
                  refine ⟨713639521464085451941733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1903038723904227871844621 713639521464085451941733)
                  ·
                    refine ⟨133807410274516022239075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 713639521464085451941733 133807410274516022239075)
                    ·
                      rfl

theorem cell23_781767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_781767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781767 prefixEnd_781767 := by exact prefixLift 781767
  have htrace : WordTrace (prefixWord ++ tailWord_781767) baseStart_781767 baseEnd_781767 := by
    simpa [prefixWord, tailWord_781767, baseEnd_781767] using wordTrace_append hprefix tailTrace_781767
  have hstable : (prefixWord ++ tailWord_781767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781767).length < 2 ^ (prefixWord ++ tailWord_781767).sum := by decide
  have hdescent : baseEnd_781767 < baseStart_781767 := by decide
  rcases family_descends (prefixWord ++ tailWord_781767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781807 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 3]
def baseStart_781807 : Nat := 118140960795 + 781807 * 2 ^ 59
def prefixEnd_781807 : Nat := 4983230072969 + 3 ^ 40 * 781807 * 2
def baseEnd_781807 : Nat := 401442770049727910217041

theorem tailTrace_781807 : CollatzResearch.WordTrace tailWord_781807 prefixEnd_781807 401442770049727910217041 := by
  unfold tailWord_781807
  simp only [CollatzResearch.WordTrace]
  refine ⟨28514843878654235850479675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19009895919102823900319783 28514843878654235850479675)
  ·
    refine ⟨42772265817981353775719513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28514843878654235850479675 42772265817981353775719513)
    ·
      refine ⟨32079199363486015331789635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42772265817981353775719513 32079199363486015331789635)
      ·
        refine ⟨48118799045229022997684453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32079199363486015331789635 48118799045229022997684453)
        ·
          refine ⟨9022274820980441812065835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48118799045229022997684453 9022274820980441812065835)
          ·
            refine ⟨13533412231470662718098753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9022274820980441812065835 13533412231470662718098753)
            ·
              refine ⟨10150059173602997038574065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13533412231470662718098753 10150059173602997038574065)
              ·
                refine ⟨7612544380202247778930549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10150059173602997038574065 7612544380202247778930549)
                ·
                  refine ⟨713676035643960729274739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7612544380202247778930549 713676035643960729274739)
                  ·
                    refine ⟨1070514053465941093912109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 713676035643960729274739 1070514053465941093912109)
                    ·
                      refine ⟨401442770049727910217041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1070514053465941093912109 401442770049727910217041)
                      ·
                        rfl

theorem cell23_781807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 1, 3].length) (baseStart_781807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781807 prefixEnd_781807 := by exact prefixLift 781807
  have htrace : WordTrace (prefixWord ++ tailWord_781807) baseStart_781807 baseEnd_781807 := by
    simpa [prefixWord, tailWord_781807, baseEnd_781807] using wordTrace_append hprefix tailTrace_781807
  have hstable : (prefixWord ++ tailWord_781807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781807).length < 2 ^ (prefixWord ++ tailWord_781807).sum := by decide
  have hdescent : baseEnd_781807 < baseStart_781807 := by decide
  rcases family_descends (prefixWord ++ tailWord_781807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781857 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 1, 6]
def baseStart_781857 : Nat := 118140960795 + 781857 * 2 ^ 59
def prefixEnd_781857 : Nat := 4983230072969 + 3 ^ 40 * 781857 * 2
def baseEnd_781857 : Nat := 133822814694150904863937

theorem tailTrace_781857 : CollatzResearch.WordTrace tailWord_781857 prefixEnd_781857 133822814694150904863937 := by
  unfold tailWord_781857
  simp only [CollatzResearch.WordTrace]
  refine ⟨28516667528473094389799825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19011111685648729593199883 28516667528473094389799825)
  ·
    refine ⟨21387500646354820792349869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28516667528473094389799825 21387500646354820792349869)
    ·
      refine ⟨8020312742383057797131201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21387500646354820792349869 8020312742383057797131201)
      ·
        refine ⟨6015234556787293347848401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8020312742383057797131201 6015234556787293347848401)
        ·
          refine ⟨4511425917590470010886301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6015234556787293347848401 4511425917590470010886301)
          ·
            refine ⟨1691784719096426254082363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4511425917590470010886301 1691784719096426254082363)
            ·
              refine ⟨2537677078644639381123545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1691784719096426254082363 2537677078644639381123545)
              ·
                refine ⟨1903257808983479535842659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537677078644639381123545 1903257808983479535842659)
                ·
                  refine ⟨2854886713475219303763989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1903257808983479535842659 2854886713475219303763989)
                  ·
                    refine ⟨133822814694150904863937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2854886713475219303763989 133822814694150904863937)
                    ·
                      rfl

theorem cell23_781857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_781857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781857 prefixEnd_781857 := by exact prefixLift 781857
  have htrace : WordTrace (prefixWord ++ tailWord_781857) baseStart_781857 baseEnd_781857 := by
    simpa [prefixWord, tailWord_781857, baseEnd_781857] using wordTrace_append hprefix tailTrace_781857
  have hstable : (prefixWord ++ tailWord_781857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781857).length < 2 ^ (prefixWord ++ tailWord_781857).sum := by decide
  have hdescent : baseEnd_781857 < baseStart_781857 := by decide
  rcases family_descends (prefixWord ++ tailWord_781857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781887 : List Nat := [1, 1, 2, 2, 3, 5, 1, 8]
def baseStart_781887 : Nat := 118140960795 + 781887 * 2 ^ 59
def prefixEnd_781887 : Nat := 4983230072969 + 3 ^ 40 * 781887 * 2
def baseEnd_781887 : Nat := 14869772166743985082099

theorem tailTrace_781887 : CollatzResearch.WordTrace tailWord_781887 prefixEnd_781887 14869772166743985082099 := by
  unfold tailWord_781887
  simp only [CollatzResearch.WordTrace]
  refine ⟨28517761718364409513391915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19011841145576273008927943 28517761718364409513391915)
  ·
    refine ⟨42776642577546614270087873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28517761718364409513391915 42776642577546614270087873)
    ·
      refine ⟨32082481933159960702565905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42776642577546614270087873 32082481933159960702565905)
      ·
        refine ⟨24061861449869970526924429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32082481933159960702565905 24061861449869970526924429)
        ·
          refine ⟨9023198043701238947596661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24061861449869970526924429 9023198043701238947596661)
          ·
            refine ⟨845924816596991151337187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9023198043701238947596661 845924816596991151337187)
            ·
              refine ⟨1268887224895486727005781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845924816596991151337187 1268887224895486727005781)
              ·
                refine ⟨14869772166743985082099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1268887224895486727005781 14869772166743985082099)
                ·
                  rfl

theorem cell23_781887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 8].length) (baseStart_781887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781887 prefixEnd_781887 := by exact prefixLift 781887
  have htrace : WordTrace (prefixWord ++ tailWord_781887) baseStart_781887 baseEnd_781887 := by
    simpa [prefixWord, tailWord_781887, baseEnd_781887] using wordTrace_append hprefix tailTrace_781887
  have hstable : (prefixWord ++ tailWord_781887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781887).length < 2 ^ (prefixWord ++ tailWord_781887).sum := by decide
  have hdescent : baseEnd_781887 < baseStart_781887 := by decide
  rcases family_descends (prefixWord ++ tailWord_781887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781907 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 4, 7, 2]
def baseStart_781907 : Nat := 118140960795 + 781907 * 2 ^ 59
def prefixEnd_781907 : Nat := 4983230072969 + 3 ^ 40 * 781907 * 2
def baseEnd_781907 : Nat := 401494118115177518966581

theorem tailTrace_781907 : CollatzResearch.WordTrace tailWord_781907 prefixEnd_781907 401494118115177518966581 := by
  unfold tailWord_781907
  simp only [CollatzResearch.WordTrace]
  refine ⟨28518491178291952929119975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19012327452194635286079983 28518491178291952929119975)
  ·
    refine ⟨42777736767437929393679963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28518491178291952929119975 42777736767437929393679963)
    ·
      refine ⟨64166605151156894090519945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42777736767437929393679963 64166605151156894090519945)
      ·
        refine ⟨48124953863367670567889959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64166605151156894090519945 48124953863367670567889959)
        ·
          refine ⟨72187430795051505851834939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48124953863367670567889959 72187430795051505851834939)
          ·
            refine ⟨108281146192577258777752409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72187430795051505851834939 108281146192577258777752409)
            ·
              refine ⟨81210859644432944083314307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108281146192577258777752409 81210859644432944083314307)
              ·
                refine ⟨121816289466649416124971461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81210859644432944083314307 121816289466649416124971461)
                ·
                  refine ⟨22840554274996765523432149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 121816289466649416124971461 22840554274996765523432149)
                  ·
                    refine ⟨535325490820236691955441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22840554274996765523432149 535325490820236691955441)
                    ·
                      refine ⟨401494118115177518966581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535325490820236691955441 401494118115177518966581)
                      ·
                        rfl

theorem cell23_781907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 7, 2].length) (baseStart_781907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781907 prefixEnd_781907 := by exact prefixLift 781907
  have htrace : WordTrace (prefixWord ++ tailWord_781907) baseStart_781907 baseEnd_781907 := by
    simpa [prefixWord, tailWord_781907, baseEnd_781907] using wordTrace_append hprefix tailTrace_781907
  have hstable : (prefixWord ++ tailWord_781907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781907).length < 2 ^ (prefixWord ++ tailWord_781907).sum := by decide
  have hdescent : baseEnd_781907 < baseStart_781907 := by decide
  rcases family_descends (prefixWord ++ tailWord_781907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_781957 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_781957 : Nat := 118140960795 + 781957 * 2 ^ 59
def prefixEnd_781957 : Nat := 4983230072969 + 3 ^ 40 * 781957 * 2
def baseEnd_781957 : Nat := 401519792147902323341351

theorem tailTrace_781957 : CollatzResearch.WordTrace tailWord_781957 prefixEnd_781957 401519792147902323341351 := by
  unfold tailWord_781957
  simp only [CollatzResearch.WordTrace]
  refine ⟨28520314828110811468440125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19013543218740540978960083 28520314828110811468440125)
  ·
    refine ⟨10695118060541554300665047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28520314828110811468440125 10695118060541554300665047)
    ·
      refine ⟨16042677090812331450997571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10695118060541554300665047 16042677090812331450997571)
      ·
        refine ⟨24064015636218497176496357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16042677090812331450997571 24064015636218497176496357)
        ·
          refine ⟨4512002931790968220593067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24064015636218497176496357 4512002931790968220593067)
          ·
            refine ⟨6768004397686452330889601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512002931790968220593067 6768004397686452330889601)
            ·
              refine ⟨5076003298264839248167201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6768004397686452330889601 5076003298264839248167201)
              ·
                refine ⟨3807002473698629436125401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5076003298264839248167201 3807002473698629436125401)
                ·
                  refine ⟨2855251855273972077094051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3807002473698629436125401 2855251855273972077094051)
                  ·
                    refine ⟨4282877782910958115641077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2855251855273972077094051 4282877782910958115641077)
                    ·
                      refine ⟨401519792147902323341351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4282877782910958115641077 401519792147902323341351)
                      ·
                        rfl

theorem cell23_781957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_781957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_781957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_781957 prefixEnd_781957 := by exact prefixLift 781957
  have htrace : WordTrace (prefixWord ++ tailWord_781957) baseStart_781957 baseEnd_781957 := by
    simpa [prefixWord, tailWord_781957, baseEnd_781957] using wordTrace_append hprefix tailTrace_781957
  have hstable : (prefixWord ++ tailWord_781957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_781957).length < 2 ^ (prefixWord ++ tailWord_781957).sum := by decide
  have hdescent : baseEnd_781957 < baseStart_781957 := by decide
  rcases family_descends (prefixWord ++ tailWord_781957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782005 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_782005 : Nat := 118140960795 + 782005 * 2 ^ 59
def prefixEnd_782005 : Nat := 4983230072969 + 3 ^ 40 * 782005 * 2
def baseEnd_782005 : Nat := 401544439219318135541131

theorem tailTrace_782005 : CollatzResearch.WordTrace tailWord_782005 prefixEnd_782005 401544439219318135541131 := by
  unfold tailWord_782005
  simp only [CollatzResearch.WordTrace]
  refine ⟨28522065531936915666187469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19014710354624610444124979 28522065531936915666187469)
  ·
    refine ⟨10695774574476343374820301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28522065531936915666187469 10695774574476343374820301)
    ·
      refine ⟨4010915465428628765557613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10695774574476343374820301 4010915465428628765557613)
      ·
        refine ⟨1504093299535735787084105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4010915465428628765557613 1504093299535735787084105)
        ·
          refine ⟨1128069974651801840313079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1504093299535735787084105 1128069974651801840313079)
          ·
            refine ⟨1692104961977702760469619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128069974651801840313079 1692104961977702760469619)
            ·
              refine ⟨2538157442966554140704429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692104961977702760469619 2538157442966554140704429)
              ·
                refine ⟨951809041112457802764161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2538157442966554140704429 951809041112457802764161)
                ·
                  refine ⟨713856780834343352073121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 951809041112457802764161 713856780834343352073121)
                  ·
                    refine ⟨535392585625757514054841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 713856780834343352073121 535392585625757514054841)
                    ·
                      refine ⟨401544439219318135541131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535392585625757514054841 401544439219318135541131)
                      ·
                        rfl

theorem cell23_782005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_782005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782005 prefixEnd_782005 := by exact prefixLift 782005
  have htrace : WordTrace (prefixWord ++ tailWord_782005) baseStart_782005 baseEnd_782005 := by
    simpa [prefixWord, tailWord_782005, baseEnd_782005] using wordTrace_append hprefix tailTrace_782005
  have hstable : (prefixWord ++ tailWord_782005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782005).length < 2 ^ (prefixWord ++ tailWord_782005).sum := by decide
  have hdescent : baseEnd_782005 < baseStart_782005 := by decide
  rcases family_descends (prefixWord ++ tailWord_782005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782024 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 2, 5]
def baseStart_782024 : Nat := 118140960795 + 782024 * 2 ^ 59
def prefixEnd_782024 : Nat := 4983230072969 + 3 ^ 40 * 782024 * 2
def baseEnd_782024 : Nat := 133851398450584520401181

theorem tailTrace_782024 : CollatzResearch.WordTrace tailWord_782024 prefixEnd_782024 133851398450584520401181 := by
  unfold tailWord_782024
  simp only [CollatzResearch.WordTrace]
  refine ⟨14261379259434040955564563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19015172345912054607419417 14261379259434040955564563)
  ·
    refine ⟨21392068889151061433346845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14261379259434040955564563 21392068889151061433346845)
    ·
      refine ⟨8022025833431648037505067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21392068889151061433346845 8022025833431648037505067)
      ·
        refine ⟨12033038750147472056257601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8022025833431648037505067 12033038750147472056257601)
        ·
          refine ⟨9024779062610604042193201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12033038750147472056257601 9024779062610604042193201)
          ·
            refine ⟨6768584296957953031644901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9024779062610604042193201 6768584296957953031644901)
            ·
              refine ⟨1269109555679616193433419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6768584296957953031644901 1269109555679616193433419)
              ·
                refine ⟨1903664333519424290150129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269109555679616193433419 1903664333519424290150129)
                ·
                  refine ⟨1427748250139568217612597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1903664333519424290150129 1427748250139568217612597)
                  ·
                    refine ⟨133851398450584520401181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1427748250139568217612597 133851398450584520401181)
                    ·
                      rfl

theorem cell23_782024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_782024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782024 prefixEnd_782024 := by exact prefixLift 782024
  have htrace : WordTrace (prefixWord ++ tailWord_782024) baseStart_782024 baseEnd_782024 := by
    simpa [prefixWord, tailWord_782024, baseEnd_782024] using wordTrace_append hprefix tailTrace_782024
  have hstable : (prefixWord ++ tailWord_782024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782024).length < 2 ^ (prefixWord ++ tailWord_782024).sum := by decide
  have hdescent : baseEnd_782024 < baseStart_782024 := by decide
  rcases family_descends (prefixWord ++ tailWord_782024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782027 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 4]
def baseStart_782027 : Nat := 118140960795 + 782027 * 2 ^ 59
def prefixEnd_782027 : Nat := 4983230072969 + 3 ^ 40 * 782027 * 2
def baseEnd_782027 : Nat := 401555735793717049466029

theorem tailTrace_782027 : CollatzResearch.WordTrace tailWord_782027 prefixEnd_782027 401555735793717049466029 := by
  unfold tailWord_782027
  simp only [CollatzResearch.WordTrace]
  refine ⟨28522867937857213423488335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19015245291904808948992223 28522867937857213423488335)
  ·
    refine ⟨42784301906785820135232503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28522867937857213423488335 42784301906785820135232503)
    ·
      refine ⟨64176452860178730202848755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42784301906785820135232503 64176452860178730202848755)
      ·
        refine ⟨96264679290268095304273133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64176452860178730202848755 96264679290268095304273133)
        ·
          refine ⟨36099254733850535739102425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96264679290268095304273133 36099254733850535739102425)
          ·
            refine ⟨27074441050387901804326819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36099254733850535739102425 27074441050387901804326819)
            ·
              refine ⟨40611661575581852706490229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27074441050387901804326819 40611661575581852706490229)
              ·
                refine ⟨3807343272710798691233459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40611661575581852706490229 3807343272710798691233459)
                ·
                  refine ⟨5711014909066198036850189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807343272710798691233459 5711014909066198036850189)
                  ·
                    refine ⟨2141630590899824263818821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5711014909066198036850189 2141630590899824263818821)
                    ·
                      refine ⟨401555735793717049466029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2141630590899824263818821 401555735793717049466029)
                      ·
                        rfl

theorem cell23_782027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 4].length) (baseStart_782027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782027 prefixEnd_782027 := by exact prefixLift 782027
  have htrace : WordTrace (prefixWord ++ tailWord_782027) baseStart_782027 baseEnd_782027 := by
    simpa [prefixWord, tailWord_782027, baseEnd_782027] using wordTrace_append hprefix tailTrace_782027
  have hstable : (prefixWord ++ tailWord_782027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782027).length < 2 ^ (prefixWord ++ tailWord_782027).sum := by decide
  have hdescent : baseEnd_782027 < baseStart_782027 := by decide
  rcases family_descends (prefixWord ++ tailWord_782027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782034 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_782034 : Nat := 118140960795 + 782034 * 2 ^ 59
def prefixEnd_782034 : Nat := 4983230072969 + 3 ^ 40 * 782034 * 2
def baseEnd_782034 : Nat := 401559330158298522078497

theorem tailTrace_782034 : CollatzResearch.WordTrace tailWord_782034 prefixEnd_782034 401559330158298522078497 := by
  unfold tailWord_782034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7130780812207963404748289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19015415499221235745995437 7130780812207963404748289)
  ·
    refine ⟨5348085609155972553561217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7130780812207963404748289 5348085609155972553561217)
    ·
      refine ⟨4011064206866979415170913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5348085609155972553561217 4011064206866979415170913)
      ·
        refine ⟨3008298155150234561378185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4011064206866979415170913 3008298155150234561378185)
        ·
          refine ⟨2256223616362675921033639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3008298155150234561378185 2256223616362675921033639)
          ·
            refine ⟨3384335424544013881550459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2256223616362675921033639 3384335424544013881550459)
            ·
              refine ⟨5076503136816020822325689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384335424544013881550459 5076503136816020822325689)
              ·
                refine ⟨3807377352612015616744267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5076503136816020822325689 3807377352612015616744267)
                ·
                  refine ⟨5711066028918023425116401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3807377352612015616744267 5711066028918023425116401)
                  ·
                    refine ⟨4283299521688517568837301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5711066028918023425116401 4283299521688517568837301)
                    ·
                      refine ⟨401559330158298522078497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4283299521688517568837301 401559330158298522078497)
                      ·
                        rfl

theorem cell23_782034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_782034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782034 prefixEnd_782034 := by exact prefixLift 782034
  have htrace : WordTrace (prefixWord ++ tailWord_782034) baseStart_782034 baseEnd_782034 := by
    simpa [prefixWord, tailWord_782034, baseEnd_782034] using wordTrace_append hprefix tailTrace_782034
  have hstable : (prefixWord ++ tailWord_782034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782034).length < 2 ^ (prefixWord ++ tailWord_782034).sum := by decide
  have hdescent : baseEnd_782034 < baseStart_782034 := by decide
  rcases family_descends (prefixWord ++ tailWord_782034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782047 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_782047 : Nat := 118140960795 + 782047 * 2 ^ 59
def prefixEnd_782047 : Nat := 4983230072969 + 3 ^ 40 * 782047 * 2
def baseEnd_782047 : Nat := 401566005406806971215937

theorem tailTrace_782047 : CollatzResearch.WordTrace tailWord_782047 prefixEnd_782047 401566005406806971215937 := by
  unfold tailWord_782047
  simp only [CollatzResearch.WordTrace]
  refine ⟨28523597397784756839216395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19015731598523171226144263 28523597397784756839216395)
  ·
    refine ⟨42785396096677135258824593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28523597397784756839216395 42785396096677135258824593)
    ·
      refine ⟨32089047072507851444118445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42785396096677135258824593 32089047072507851444118445)
      ·
        refine ⟨12033392652190444291544417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32089047072507851444118445 12033392652190444291544417)
        ·
          refine ⟨9025044489142833218658313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12033392652190444291544417 9025044489142833218658313)
          ·
            refine ⟨6768783366857124913993735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9025044489142833218658313 6768783366857124913993735)
            ·
              refine ⟨10153175050285687370990603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6768783366857124913993735 10153175050285687370990603)
              ·
                refine ⟨15229762575428531056485905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10153175050285687370990603 15229762575428531056485905)
                ·
                  refine ⟨11422321931571398292364429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15229762575428531056485905 11422321931571398292364429)
                  ·
                    refine ⟨4283370724339274359636661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11422321931571398292364429 4283370724339274359636661)
                    ·
                      refine ⟨401566005406806971215937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4283370724339274359636661 401566005406806971215937)
                      ·
                        rfl

theorem cell23_782047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_782047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782047 prefixEnd_782047 := by exact prefixLift 782047
  have htrace : WordTrace (prefixWord ++ tailWord_782047) baseStart_782047 baseEnd_782047 := by
    simpa [prefixWord, tailWord_782047, baseEnd_782047] using wordTrace_append hprefix tailTrace_782047
  have hstable : (prefixWord ++ tailWord_782047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782047).length < 2 ^ (prefixWord ++ tailWord_782047).sum := by decide
  have hdescent : baseEnd_782047 < baseStart_782047 := by decide
  rcases family_descends (prefixWord ++ tailWord_782047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782057 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_782057 : Nat := 118140960795 + 782057 * 2 ^ 59
def prefixEnd_782057 : Nat := 4983230072969 + 3 ^ 40 * 782057 * 2
def baseEnd_782057 : Nat := 401571140213351932090891

theorem tailTrace_782057 : CollatzResearch.WordTrace tailWord_782057 prefixEnd_782057 401571140213351932090891 := by
  unfold tailWord_782057
  simp only [CollatzResearch.WordTrace]
  refine ⟨28523962127748528547080425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19015974751832352364720283 28523962127748528547080425)
  ·
    refine ⟨21392971595811396410310319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28523962127748528547080425 21392971595811396410310319)
    ·
      refine ⟨32089457393717094615465479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21392971595811396410310319 32089457393717094615465479)
      ·
        refine ⟨48134186090575641923198219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32089457393717094615465479 48134186090575641923198219)
        ·
          refine ⟨72201279135863462884797329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48134186090575641923198219 72201279135863462884797329)
          ·
            refine ⟨54150959351897597163597997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72201279135863462884797329 54150959351897597163597997)
            ·
              refine ⟨20306609756961598936349249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54150959351897597163597997 20306609756961598936349249)
              ·
                refine ⟨15229957317721199202261937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20306609756961598936349249 15229957317721199202261937)
                ·
                  refine ⟨11422467988290899401696453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15229957317721199202261937 11422467988290899401696453)
                  ·
                    refine ⟨2141712747804543637818085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11422467988290899401696453 2141712747804543637818085)
                    ·
                      refine ⟨401571140213351932090891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2141712747804543637818085 401571140213351932090891)
                      ·
                        rfl

theorem cell23_782057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_782057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782057 prefixEnd_782057 := by exact prefixLift 782057
  have htrace : WordTrace (prefixWord ++ tailWord_782057) baseStart_782057 baseEnd_782057 := by
    simpa [prefixWord, tailWord_782057, baseEnd_782057] using wordTrace_append hprefix tailTrace_782057
  have hstable : (prefixWord ++ tailWord_782057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782057).length < 2 ^ (prefixWord ++ tailWord_782057).sum := by decide
  have hdescent : baseEnd_782057 < baseStart_782057 := by decide
  rcases family_descends (prefixWord ++ tailWord_782057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782061 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 1, 6, 2]
def baseStart_782061 : Nat := 118140960795 + 782061 * 2 ^ 59
def prefixEnd_782061 : Nat := 4983230072969 + 3 ^ 40 * 782061 * 2
def baseEnd_782061 : Nat := 401573194135969916440873

theorem tailTrace_782061 : CollatzResearch.WordTrace tailWord_782061 prefixEnd_782061 401573194135969916440873 := by
  unfold tailWord_782061
  simp only [CollatzResearch.WordTrace]
  refine ⟨28524108019734037230226037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19016072013156024820150691 28524108019734037230226037)
  ·
    refine ⟨2674135126850065990333691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28524108019734037230226037 2674135126850065990333691)
    ·
      refine ⟨4011202690275098985500537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2674135126850065990333691 4011202690275098985500537)
      ·
        refine ⟨3008402017706324239125403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4011202690275098985500537 3008402017706324239125403)
        ·
          refine ⟨4512603026559486358688105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008402017706324239125403 4512603026559486358688105)
          ·
            refine ⟨3384452269919614769016079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4512603026559486358688105 3384452269919614769016079)
            ·
              refine ⟨5076678404879422153524119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3384452269919614769016079 5076678404879422153524119)
              ·
                refine ⟨7615017607319133230286179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5076678404879422153524119 7615017607319133230286179)
                ·
                  refine ⟨11422526410978699845429269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7615017607319133230286179 11422526410978699845429269)
                  ·
                    refine ⟨535430925514626555254497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11422526410978699845429269 535430925514626555254497)
                    ·
                      refine ⟨401573194135969916440873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 535430925514626555254497 401573194135969916440873)
                      ·
                        rfl

theorem cell23_782061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_782061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782061 prefixEnd_782061 := by exact prefixLift 782061
  have htrace : WordTrace (prefixWord ++ tailWord_782061) baseStart_782061 baseEnd_782061 := by
    simpa [prefixWord, tailWord_782061, baseEnd_782061] using wordTrace_append hprefix tailTrace_782061
  have hstable : (prefixWord ++ tailWord_782061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782061).length < 2 ^ (prefixWord ++ tailWord_782061).sum := by decide
  have hdescent : baseEnd_782061 < baseStart_782061 := by decide
  rcases family_descends (prefixWord ++ tailWord_782061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782081 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_782081 : Nat := 118140960795 + 782081 * 2 ^ 59
def prefixEnd_782081 : Nat := 4983230072969 + 3 ^ 40 * 782081 * 2
def baseEnd_782081 : Nat := 401583463749059838190781

theorem tailTrace_782081 : CollatzResearch.WordTrace tailWord_782081 prefixEnd_782081 401583463749059838190781 := by
  unfold tailWord_782081
  simp only [CollatzResearch.WordTrace]
  refine ⟨28524837479661580645954097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19016558319774387097302731 28524837479661580645954097)
  ·
    refine ⟨21393628109746185484465573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28524837479661580645954097 21393628109746185484465573)
    ·
      refine ⟨4011305270577409778337295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21393628109746185484465573 4011305270577409778337295)
      ·
        refine ⟨6016957905866114667505943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4011305270577409778337295 6016957905866114667505943)
        ·
          refine ⟨9025436858799172001258915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6016957905866114667505943 9025436858799172001258915)
          ·
            refine ⟨13538155288198758001888373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9025436858799172001258915 13538155288198758001888373)
            ·
              refine ⟨1269202058268633562677035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13538155288198758001888373 1269202058268633562677035)
              ·
                refine ⟨1903803087402950344015553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269202058268633562677035 1903803087402950344015553)
                ·
                  refine ⟨1427852315552212758011665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1903803087402950344015553 1427852315552212758011665)
                  ·
                    refine ⟨1070889236664159568508749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1427852315552212758011665 1070889236664159568508749)
                    ·
                      refine ⟨401583463749059838190781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1070889236664159568508749 401583463749059838190781)
                      ·
                        rfl

theorem cell23_782081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_782081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782081 prefixEnd_782081 := by exact prefixLift 782081
  have htrace : WordTrace (prefixWord ++ tailWord_782081) baseStart_782081 baseEnd_782081 := by
    simpa [prefixWord, tailWord_782081, baseEnd_782081] using wordTrace_append hprefix tailTrace_782081
  have hstable : (prefixWord ++ tailWord_782081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782081).length < 2 ^ (prefixWord ++ tailWord_782081).sum := by decide
  have hdescent : baseEnd_782081 < baseStart_782081 := by decide
  rcases family_descends (prefixWord ++ tailWord_782081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782088 : List Nat := [2, 1, 3, 2, 2, 1, 4, 3, 1, 4]
def baseStart_782088 : Nat := 118140960795 + 782088 * 2 ^ 59
def prefixEnd_782088 : Nat := 4983230072969 + 3 ^ 40 * 782088 * 2
def baseEnd_782088 : Nat := 133862352704547103601083

theorem tailTrace_782088 : CollatzResearch.WordTrace tailWord_782088 prefixEnd_782088 133862352704547103601083 := by
  unfold tailWord_782088
  simp only [CollatzResearch.WordTrace]
  refine ⟨14262546395318110420729459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19016728527090813894305945 14262546395318110420729459)
  ·
    refine ⟨21393819592977165631094189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14262546395318110420729459 21393819592977165631094189)
    ·
      refine ⟨8022682347366437111660321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21393819592977165631094189 8022682347366437111660321)
      ·
        refine ⟨6017011760524827833745241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8022682347366437111660321 6017011760524827833745241)
        ·
          refine ⟨4512758820393620875308931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6017011760524827833745241 4512758820393620875308931)
          ·
            refine ⟨6769138230590431312963397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512758820393620875308931 6769138230590431312963397)
            ·
              refine ⟨1269213418235705871180637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6769138230590431312963397 1269213418235705871180637)
              ·
                refine ⟨475955031838389701692739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1269213418235705871180637 475955031838389701692739)
                ·
                  refine ⟨713932547757584552539109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475955031838389701692739 713932547757584552539109)
                  ·
                    refine ⟨133862352704547103601083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 713932547757584552539109 133862352704547103601083)
                    ·
                      rfl

theorem cell23_782088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_782088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782088 prefixEnd_782088 := by exact prefixLift 782088
  have htrace : WordTrace (prefixWord ++ tailWord_782088) baseStart_782088 baseEnd_782088 := by
    simpa [prefixWord, tailWord_782088, baseEnd_782088] using wordTrace_append hprefix tailTrace_782088
  have hstable : (prefixWord ++ tailWord_782088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782088).length < 2 ^ (prefixWord ++ tailWord_782088).sum := by decide
  have hdescent : baseEnd_782088 < baseStart_782088 := by decide
  rcases family_descends (prefixWord ++ tailWord_782088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782101 : List Nat := [1, 3, 2, 1, 2, 5, 1, 2, 6]
def baseStart_782101 : Nat := 118140960795 + 782101 * 2 ^ 59
def prefixEnd_782101 : Nat := 4983230072969 + 3 ^ 40 * 782101 * 2
def baseEnd_782101 : Nat := 44621525929127751104521

theorem tailTrace_782101 : CollatzResearch.WordTrace tailWord_782101 prefixEnd_782101 44621525929127751104521 := by
  unfold tailWord_782101
  simp only [CollatzResearch.WordTrace]
  refine ⟨28525566939589124061682157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19017044626392749374454771 28525566939589124061682157)
  ·
    refine ⟨10697087602345921523130809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28525566939589124061682157 10697087602345921523130809)
    ·
      refine ⟨8022815701759441142348107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10697087602345921523130809 8022815701759441142348107)
      ·
        refine ⟨12034223552639161713522161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8022815701759441142348107 12034223552639161713522161)
        ·
          refine ⟨9025667664479371285141621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12034223552639161713522161 9025667664479371285141621)
          ·
            refine ⟨846156343544941057982027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9025667664479371285141621 846156343544941057982027)
            ·
              refine ⟨1269234515317411586973041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846156343544941057982027 1269234515317411586973041)
              ·
                refine ⟨951925886488058690229781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269234515317411586973041 951925886488058690229781)
                ·
                  refine ⟨44621525929127751104521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 951925886488058690229781 44621525929127751104521)
                  ·
                    rfl

theorem cell23_782101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_782101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782101 prefixEnd_782101 := by exact prefixLift 782101
  have htrace : WordTrace (prefixWord ++ tailWord_782101) baseStart_782101 baseEnd_782101 := by
    simpa [prefixWord, tailWord_782101, baseEnd_782101] using wordTrace_append hprefix tailTrace_782101
  have hstable : (prefixWord ++ tailWord_782101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782101).length < 2 ^ (prefixWord ++ tailWord_782101).sum := by decide
  have hdescent : baseEnd_782101 < baseStart_782101 := by decide
  rcases family_descends (prefixWord ++ tailWord_782101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_782107 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 5]
def baseStart_782107 : Nat := 118140960795 + 782107 * 2 ^ 59
def prefixEnd_782107 : Nat := 4983230072969 + 3 ^ 40 * 782107 * 2
def baseEnd_782107 : Nat := 401596814246076736465661

theorem tailTrace_782107 : CollatzResearch.WordTrace tailWord_782107 prefixEnd_782107 401596814246076736465661 := by
  unfold tailWord_782107
  simp only [CollatzResearch.WordTrace]
  refine ⟨28525785777567387086400575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19017190518378258057600383 28525785777567387086400575)
  ·
    refine ⟨42788678666351080629600863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28525785777567387086400575 42788678666351080629600863)
    ·
      refine ⟨64183017999526620944401295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42788678666351080629600863 64183017999526620944401295)
      ·
        refine ⟨96274526999289931416601943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64183017999526620944401295 96274526999289931416601943)
        ·
          refine ⟨144411790498934897124902915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96274526999289931416601943 144411790498934897124902915)
          ·
            refine ⟨216617685748402345687354373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144411790498934897124902915 216617685748402345687354373)
            ·
              refine ⟨40615816077825439816378945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 216617685748402345687354373 40615816077825439816378945)
              ·
                refine ⟨30461862058369079862284209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40615816077825439816378945 30461862058369079862284209)
                ·
                  refine ⟨22846396543776809896713157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30461862058369079862284209 22846396543776809896713157)
                  ·
                    refine ⟨4283699351958151855633717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22846396543776809896713157 4283699351958151855633717)
                    ·
                      refine ⟨401596814246076736465661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4283699351958151855633717 401596814246076736465661)
                      ·
                        rfl

theorem cell23_782107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_782107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_782107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_782107 prefixEnd_782107 := by exact prefixLift 782107
  have htrace : WordTrace (prefixWord ++ tailWord_782107) baseStart_782107 baseEnd_782107 := by
    simpa [prefixWord, tailWord_782107, baseEnd_782107] using wordTrace_append hprefix tailTrace_782107
  have hstable : (prefixWord ++ tailWord_782107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_782107).length < 2 ^ (prefixWord ++ tailWord_782107).sum := by decide
  have hdescent : baseEnd_782107 < baseStart_782107 := by decide
  rcases family_descends (prefixWord ++ tailWord_782107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
