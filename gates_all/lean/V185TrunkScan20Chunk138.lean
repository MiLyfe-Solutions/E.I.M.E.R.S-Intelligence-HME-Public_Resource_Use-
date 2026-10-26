import V185TrunkScan20Chunk137

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_838798 : List Nat := [4, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_838798 : Nat := 118140960795 + 838798 * 2 ^ 59
def prefixEnd_838798 : Nat := 4983230072969 + 3 ^ 40 * 838798 * 2
def baseEnd_838798 : Nat := 382850263137879495704395

theorem tailTrace_838798 : CollatzResearch.WordTrace tailWord_838798 prefixEnd_838798 382850263137879495704395 := by
  unfold tailWord_838798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824184551898197017296631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20395650943457050758915365 3824184551898197017296631)
  ·
    refine ⟨5736276827847295525944947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3824184551898197017296631 5736276827847295525944947)
    ·
      refine ⟨8604415241770943288917421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5736276827847295525944947 8604415241770943288917421)
      ·
        refine ⟨3226655715664103733344033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8604415241770943288917421 3226655715664103733344033)
        ·
          refine ⟨2419991786748077800008025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3226655715664103733344033 2419991786748077800008025)
          ·
            refine ⟨1814993840061058350006019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419991786748077800008025 1814993840061058350006019)
            ·
              refine ⟨2722490760091587525009029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814993840061058350006019 2722490760091587525009029)
              ·
                refine ⟨510467017517172660939193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2722490760091587525009029 510467017517172660939193)
                ·
                  refine ⟨382850263137879495704395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510467017517172660939193 382850263137879495704395)
                  ·
                    rfl

theorem cell20_838798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_838798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838798 prefixEnd_838798 := by exact prefixLift 838798
  have htrace : WordTrace (prefixWord ++ tailWord_838798) baseStart_838798 baseEnd_838798 := by
    simpa [prefixWord, tailWord_838798, baseEnd_838798] using wordTrace_append hprefix tailTrace_838798
  have hstable : (prefixWord ++ tailWord_838798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838798).length < 2 ^ (prefixWord ++ tailWord_838798).sum := by decide
  have hdescent : baseEnd_838798 < baseStart_838798 := by decide
  rcases family_descends (prefixWord ++ tailWord_838798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838892 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_838892 : Nat := 118140960795 + 838892 * 2 ^ 59
def prefixEnd_838892 : Nat := 4983230072969 + 3 ^ 40 * 838892 * 2
def baseEnd_838892 : Nat := 382893167299232946570677

theorem tailTrace_838892 : CollatzResearch.WordTrace tailWord_838892 prefixEnd_838892 382893167299232946570677 := by
  unfold tailWord_838892
  simp only [CollatzResearch.WordTrace]
  refine ⟨15298452438422515096147465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20397936584563353461529953 15298452438422515096147465)
  ·
    refine ⟨11473839328816886322110599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15298452438422515096147465 11473839328816886322110599)
    ·
      refine ⟨17210758993225329483165899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11473839328816886322110599 17210758993225329483165899)
      ·
        refine ⟨25816138489837994224748849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17210758993225329483165899 25816138489837994224748849)
        ·
          refine ⟨19362103867378495668561637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25816138489837994224748849 19362103867378495668561637)
          ·
            refine ⟨3630394475133467937855307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19362103867378495668561637 3630394475133467937855307)
            ·
              refine ⟨5445591712700201906782961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630394475133467937855307 5445591712700201906782961)
              ·
                refine ⟨4084193784525151430087221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5445591712700201906782961 4084193784525151430087221)
                ·
                  refine ⟨382893167299232946570677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4084193784525151430087221 382893167299232946570677)
                  ·
                    rfl

theorem cell20_838892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_838892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838892 prefixEnd_838892 := by exact prefixLift 838892
  have htrace : WordTrace (prefixWord ++ tailWord_838892) baseStart_838892 baseEnd_838892 := by
    simpa [prefixWord, tailWord_838892, baseEnd_838892] using wordTrace_append hprefix tailTrace_838892
  have hstable : (prefixWord ++ tailWord_838892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838892).length < 2 ^ (prefixWord ++ tailWord_838892).sum := by decide
  have hdescent : baseEnd_838892 < baseStart_838892 := by decide
  rcases family_descends (prefixWord ++ tailWord_838892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838923 : List Nat := [1, 1, 1, 1, 5, 4, 2, 5]
def baseStart_838923 : Nat := 118140960795 + 838923 * 2 ^ 59
def prefixEnd_838923 : Nat := 4983230072969 + 3 ^ 40 * 838923 * 2
def baseEnd_838923 : Nat := 127635772181311538845739

theorem tailTrace_838923 : CollatzResearch.WordTrace tailWord_838923 prefixEnd_838923 127635772181311538845739 := by
  unfold tailWord_838923
  simp only [CollatzResearch.WordTrace]
  refine ⟨30598035539732722486673423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20398690359821814991115615 30598035539732722486673423)
  ·
    refine ⟨45897053309599083730010135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30598035539732722486673423 45897053309599083730010135)
    ·
      refine ⟨68845579964398625595015203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45897053309599083730010135 68845579964398625595015203)
      ·
        refine ⟨103268369946597938392522805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68845579964398625595015203 103268369946597938392522805)
        ·
          refine ⟨9681409682493556724299013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103268369946597938392522805 9681409682493556724299013)
          ·
            refine ⟨1815264315467541885806065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9681409682493556724299013 1815264315467541885806065)
            ·
              refine ⟨1361448236600656414354549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1815264315467541885806065 1361448236600656414354549)
              ·
                refine ⟨127635772181311538845739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1361448236600656414354549 127635772181311538845739)
                ·
                  rfl

theorem cell20_838923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_838923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838923 prefixEnd_838923 := by exact prefixLift 838923
  have htrace : WordTrace (prefixWord ++ tailWord_838923) baseStart_838923 baseEnd_838923 := by
    simpa [prefixWord, tailWord_838923, baseEnd_838923] using wordTrace_append hprefix tailTrace_838923
  have hstable : (prefixWord ++ tailWord_838923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838923).length < 2 ^ (prefixWord ++ tailWord_838923).sum := by decide
  have hdescent : baseEnd_838923 < baseStart_838923 := by decide
  rcases family_descends (prefixWord ++ tailWord_838923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838926 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_838926 : Nat := 118140960795 + 838926 * 2 ^ 59
def prefixEnd_838926 : Nat := 4983230072969 + 3 ^ 40 * 838926 * 2
def baseEnd_838926 : Nat := 382908685825679939437205

theorem tailTrace_838926 : CollatzResearch.WordTrace tailWord_838926 prefixEnd_838926 382908685825679939437205 := by
  unfold tailWord_838926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824768119840231749879079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20398763305814569332688421 3824768119840231749879079)
  ·
    refine ⟨5737152179760347624818619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3824768119840231749879079 5737152179760347624818619)
    ·
      refine ⟨8605728269640521437227929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5737152179760347624818619 8605728269640521437227929)
      ·
        refine ⟨6454296202230391077920947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8605728269640521437227929 6454296202230391077920947)
        ·
          refine ⟨9681444303345586616881421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454296202230391077920947 9681444303345586616881421)
          ·
            refine ⟨3630541613754594981330533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9681444303345586616881421 3630541613754594981330533)
            ·
              refine ⟨680726552578986558999475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3630541613754594981330533 680726552578986558999475)
              ·
                refine ⟨1021089828868479838499213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680726552578986558999475 1021089828868479838499213)
                ·
                  refine ⟨382908685825679939437205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021089828868479838499213 382908685825679939437205)
                  ·
                    rfl

theorem cell20_838926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_838926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838926 prefixEnd_838926 := by exact prefixLift 838926
  have htrace : WordTrace (prefixWord ++ tailWord_838926) baseStart_838926 baseEnd_838926 := by
    simpa [prefixWord, tailWord_838926, baseEnd_838926] using wordTrace_append hprefix tailTrace_838926
  have hstable : (prefixWord ++ tailWord_838926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838926).length < 2 ^ (prefixWord ++ tailWord_838926).sum := by decide
  have hdescent : baseEnd_838926 < baseStart_838926 := by decide
  rcases family_descends (prefixWord ++ tailWord_838926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838964 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_838964 : Nat := 118140960795 + 838964 * 2 ^ 59
def prefixEnd_838964 : Nat := 4983230072969 + 3 ^ 40 * 838964 * 2
def baseEnd_838964 : Nat := 382926030061120696170383

theorem tailTrace_838964 : CollatzResearch.WordTrace tailWord_838964 prefixEnd_838964 382926030061120696170383 := by
  unfold tailWord_838964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15299765466292093244457973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20399687288389457659277297 15299765466292093244457973)
  ·
    refine ⟨1434353012464883741667935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15299765466292093244457973 1434353012464883741667935)
    ·
      refine ⟨2151529518697325612501903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1434353012464883741667935 2151529518697325612501903)
      ·
        refine ⟨3227294278045988418752855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151529518697325612501903 3227294278045988418752855)
        ·
          refine ⟨4840941417068982628129283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3227294278045988418752855 4840941417068982628129283)
          ·
            refine ⟨7261412125603473942193925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4840941417068982628129283 7261412125603473942193925)
            ·
              refine ⟨1361514773550651364161361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7261412125603473942193925 1361514773550651364161361)
              ·
                refine ⟨1021136080162988523121021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361514773550651364161361 1021136080162988523121021)
                ·
                  refine ⟨382926030061120696170383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021136080162988523121021 382926030061120696170383)
                  ·
                    rfl

theorem cell20_838964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_838964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_838964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_838964 prefixEnd_838964 := by exact prefixLift 838964
  have htrace : WordTrace (prefixWord ++ tailWord_838964) baseStart_838964 baseEnd_838964 := by
    simpa [prefixWord, tailWord_838964, baseEnd_838964] using wordTrace_append hprefix tailTrace_838964
  have hstable : (prefixWord ++ tailWord_838964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838964).length < 2 ^ (prefixWord ++ tailWord_838964).sum := by decide
  have hdescent : baseEnd_838964 < baseStart_838964 := by decide
  rcases family_descends (prefixWord ++ tailWord_838964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839013 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_839013 : Nat := 118140960795 + 839013 * 2 ^ 59
def prefixEnd_839013 : Nat := 4983230072969 + 3 ^ 40 * 839013 * 2
def baseEnd_839013 : Nat := 382948394996294303536849

theorem tailTrace_839013 : CollatzResearch.WordTrace tailWord_839013 prefixEnd_839013 382948394996294303536849 := by
  unfold tailWord_839013
  simp only [CollatzResearch.WordTrace]
  refine ⟨30601318109406667857449693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20400878739604445238299795 30601318109406667857449693)
  ·
    refine ⟨11475494291027500446543635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30601318109406667857449693 11475494291027500446543635)
    ·
      refine ⟨17213241436541250669815453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11475494291027500446543635 17213241436541250669815453)
      ·
        refine ⟨6454965538702969001180795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17213241436541250669815453 6454965538702969001180795)
        ·
          refine ⟨9682448308054453501771193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454965538702969001180795 9682448308054453501771193)
          ·
            refine ⟨7261836231040840126328395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9682448308054453501771193 7261836231040840126328395)
            ·
              refine ⟨10892754346561260189492593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7261836231040840126328395 10892754346561260189492593)
              ·
                refine ⟨8169565759920945142119445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10892754346561260189492593 8169565759920945142119445)
                ·
                  refine ⟨382948394996294303536849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8169565759920945142119445 382948394996294303536849)
                  ·
                    rfl

theorem cell20_839013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_839013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839013 prefixEnd_839013 := by exact prefixLift 839013
  have htrace : WordTrace (prefixWord ++ tailWord_839013) baseStart_839013 baseEnd_839013 := by
    simpa [prefixWord, tailWord_839013, baseEnd_839013] using wordTrace_append hprefix tailTrace_839013
  have hstable : (prefixWord ++ tailWord_839013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839013).length < 2 ^ (prefixWord ++ tailWord_839013).sum := by decide
  have hdescent : baseEnd_839013 < baseStart_839013 := by decide
  rcases family_descends (prefixWord ++ tailWord_839013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839051 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 4]
def baseStart_839051 : Nat := 118140960795 + 839051 * 2 ^ 59
def prefixEnd_839051 : Nat := 4983230072969 + 3 ^ 40 * 839051 * 2
def baseEnd_839051 : Nat := 382965739231735060270027

theorem tailTrace_839051 : CollatzResearch.WordTrace tailWord_839051 prefixEnd_839051 382965739231735060270027 := by
  unfold tailWord_839051
  simp only [CollatzResearch.WordTrace]
  refine ⟨30602704083269000347333007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20401802722179333564888671 30602704083269000347333007)
  ·
    refine ⟨45904056124903500520999511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30602704083269000347333007 45904056124903500520999511)
    ·
      refine ⟨68856084187355250781499267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45904056124903500520999511 68856084187355250781499267)
      ·
        refine ⟨103284126281032876172248901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68856084187355250781499267 103284126281032876172248901)
        ·
          refine ⟨19365773677693664282296669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103284126281032876172248901 19365773677693664282296669)
          ·
            refine ⟨7262165129135124105861251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19365773677693664282296669 7262165129135124105861251)
            ·
              refine ⟨10893247693702686158791877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7262165129135124105861251 10893247693702686158791877)
              ·
                refine ⟨2042483942569253654773477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10893247693702686158791877 2042483942569253654773477)
                ·
                  refine ⟨382965739231735060270027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2042483942569253654773477 382965739231735060270027)
                  ·
                    rfl

theorem cell20_839051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_839051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839051 prefixEnd_839051 := by exact prefixLift 839051
  have htrace : WordTrace (prefixWord ++ tailWord_839051) baseStart_839051 baseEnd_839051 := by
    simpa [prefixWord, tailWord_839051, baseEnd_839051] using wordTrace_append hprefix tailTrace_839051
  have hstable : (prefixWord ++ tailWord_839051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839051).length < 2 ^ (prefixWord ++ tailWord_839051).sum := by decide
  have hdescent : baseEnd_839051 < baseStart_839051 := by decide
  rcases family_descends (prefixWord ++ tailWord_839051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839054 : List Nat := [4, 1, 1, 4, 2, 1, 1, 6]
def baseStart_839054 : Nat := 118140960795 + 839054 * 2 ^ 59
def prefixEnd_839054 : Nat := 4983230072969 + 3 ^ 40 * 839054 * 2
def baseEnd_839054 : Nat := 127655702837826794390005

theorem tailTrace_839054 : CollatzResearch.WordTrace tailWord_839054 prefixEnd_839054 127655702837826794390005 := by
  unfold tailWord_839054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825351687782266482461527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20401875668172087906461477 3825351687782266482461527)
  ·
    refine ⟨5738027531673399723692291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3825351687782266482461527 5738027531673399723692291)
    ·
      refine ⟨8607041297510099585538437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738027531673399723692291 8607041297510099585538437)
      ·
        refine ⟨1613820243283143672288457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8607041297510099585538437 1613820243283143672288457)
        ·
          refine ⟨1210365182462357754216343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1613820243283143672288457 1210365182462357754216343)
          ·
            refine ⟨1815547773693536631324515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210365182462357754216343 1815547773693536631324515)
            ·
              refine ⟨2723321660540304946986773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815547773693536631324515 2723321660540304946986773)
              ·
                refine ⟨127655702837826794390005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2723321660540304946986773 127655702837826794390005)
                ·
                  rfl

theorem cell20_839054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_839054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839054 prefixEnd_839054 := by exact prefixLift 839054
  have htrace : WordTrace (prefixWord ++ tailWord_839054) baseStart_839054 baseEnd_839054 := by
    simpa [prefixWord, tailWord_839054, baseEnd_839054] using wordTrace_append hprefix tailTrace_839054
  have hstable : (prefixWord ++ tailWord_839054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839054).length < 2 ^ (prefixWord ++ tailWord_839054).sum := by decide
  have hdescent : baseEnd_839054 < baseStart_839054 := by decide
  rcases family_descends (prefixWord ++ tailWord_839054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839085 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_839085 : Nat := 118140960795 + 839085 * 2 ^ 59
def prefixEnd_839085 : Nat := 4983230072969 + 3 ^ 40 * 839085 * 2
def baseEnd_839085 : Nat := 382981257758182053136555

theorem tailTrace_839085 : CollatzResearch.WordTrace tailWord_839085 prefixEnd_839085 382981257758182053136555 := by
  unfold tailWord_839085
  simp only [CollatzResearch.WordTrace]
  refine ⟨30603944165145824154070709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20402629443430549436047139 30603944165145824154070709)
  ·
    refine ⟨2869119765482421014444129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30603944165145824154070709 2869119765482421014444129)
    ·
      refine ⟨2151839824111815760833097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2869119765482421014444129 2151839824111815760833097)
      ·
        refine ⟨1613879868083861820624823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2151839824111815760833097 1613879868083861820624823)
        ·
          refine ⟨2420819802125792730937235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613879868083861820624823 2420819802125792730937235)
          ·
            refine ⟨3631229703188689096405853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420819802125792730937235 3631229703188689096405853)
            ·
              refine ⟨1361711138695758411152195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3631229703188689096405853 1361711138695758411152195)
              ·
                refine ⟨2042566708043637616728293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361711138695758411152195 2042566708043637616728293)
                ·
                  refine ⟨382981257758182053136555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2042566708043637616728293 382981257758182053136555)
                  ·
                    rfl

theorem cell20_839085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_839085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839085 prefixEnd_839085 := by exact prefixLift 839085
  have htrace : WordTrace (prefixWord ++ tailWord_839085) baseStart_839085 baseEnd_839085 := by
    simpa [prefixWord, tailWord_839085, baseEnd_839085] using wordTrace_append hprefix tailTrace_839085
  have hstable : (prefixWord ++ tailWord_839085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839085).length < 2 ^ (prefixWord ++ tailWord_839085).sum := by decide
  have hdescent : baseEnd_839085 < baseStart_839085 := by decide
  rcases family_descends (prefixWord ++ tailWord_839085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839096 : List Nat := [2, 1, 2, 1, 2, 2, 3, 7]
def baseStart_839096 : Nat := 118140960795 + 839096 * 2 ^ 59
def prefixEnd_839096 : Nat := 4983230072969 + 3 ^ 40 * 839096 * 2
def baseEnd_839096 : Nat := 127662092819304967923281

theorem tailTrace_839096 : CollatzResearch.WordTrace tailWord_839096 prefixEnd_839096 127662092819304967923281 := by
  unfold tailWord_839096
  simp only [CollatzResearch.WordTrace]
  refine ⟨15302172684052986516360571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20402896912070648688480761 15302172684052986516360571)
  ·
    refine ⟨22953259026079479774540857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15302172684052986516360571 22953259026079479774540857)
    ·
      refine ⟨17214944269559609830905643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22953259026079479774540857 17214944269559609830905643)
      ·
        refine ⟨25822416404339414746358465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17214944269559609830905643 25822416404339414746358465)
        ·
          refine ⟨19366812303254561059768849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25822416404339414746358465 19366812303254561059768849)
          ·
            refine ⟨14525109227440920794826637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19366812303254561059768849 14525109227440920794826637)
            ·
              refine ⟨5446915960290345298059989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14525109227440920794826637 5446915960290345298059989)
              ·
                refine ⟨127662092819304967923281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5446915960290345298059989 127662092819304967923281)
                ·
                  rfl

theorem cell20_839096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_839096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839096 prefixEnd_839096 := by exact prefixLift 839096
  have htrace : WordTrace (prefixWord ++ tailWord_839096) baseStart_839096 baseEnd_839096 := by
    simpa [prefixWord, tailWord_839096, baseEnd_839096] using wordTrace_append hprefix tailTrace_839096
  have hstable : (prefixWord ++ tailWord_839096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839096).length < 2 ^ (prefixWord ++ tailWord_839096).sum := by decide
  have hdescent : baseEnd_839096 < baseStart_839096 := by decide
  rcases family_descends (prefixWord ++ tailWord_839096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839137 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 3]
def baseStart_839137 : Nat := 118140960795 + 839137 * 2 ^ 59
def prefixEnd_839137 : Nat := 4983230072969 + 3 ^ 40 * 839137 * 2
def baseEnd_839137 : Nat := 383004991975100983403009

theorem tailTrace_839137 : CollatzResearch.WordTrace tailWord_839137 prefixEnd_839137 383004991975100983403009 := by
  unfold tailWord_839137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30605840760957437034963665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20403893840638291356642443 30605840760957437034963665)
  ·
    refine ⟨22954380570718077776222749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30605840760957437034963665 22954380570718077776222749)
    ·
      refine ⟨8607892714019279166083531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22954380570718077776222749 8607892714019279166083531)
      ·
        refine ⟨12911839071028918749125297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8607892714019279166083531 12911839071028918749125297)
        ·
          refine ⟨9683879303271689061843973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12911839071028918749125297 9683879303271689061843973)
          ·
            refine ⟨1815727369363441699095745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9683879303271689061843973 1815727369363441699095745)
            ·
              refine ⟨1361795527022581274321809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1815727369363441699095745 1361795527022581274321809)
              ·
                refine ⟨1021346645266935955741357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361795527022581274321809 1021346645266935955741357)
                ·
                  refine ⟨383004991975100983403009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021346645266935955741357 383004991975100983403009)
                  ·
                    rfl

theorem cell20_839137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_839137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839137 prefixEnd_839137 := by exact prefixLift 839137
  have htrace : WordTrace (prefixWord ++ tailWord_839137) baseStart_839137 baseEnd_839137 := by
    simpa [prefixWord, tailWord_839137, baseEnd_839137] using wordTrace_append hprefix tailTrace_839137
  have hstable : (prefixWord ++ tailWord_839137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839137).length < 2 ^ (prefixWord ++ tailWord_839137).sum := by decide
  have hdescent : baseEnd_839137 < baseStart_839137 := by decide
  rcases family_descends (prefixWord ++ tailWord_839137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839165 : List Nat := [1, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_839165 : Nat := 118140960795 + 839165 * 2 ^ 59
def prefixEnd_839165 : Nat := 4983230072969 + 3 ^ 40 * 839165 * 2
def baseEnd_839165 : Nat := 383017771938057330469561

theorem tailTrace_839165 : CollatzResearch.WordTrace tailWord_839165 prefixEnd_839165 383017771938057330469561 := by
  unfold tailWord_839165
  simp only [CollatzResearch.WordTrace]
  refine ⟨30606862004855997816982949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20404574669903998544655299 30606862004855997816982949)
  ·
    refine ⟨5738786625910499590684303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30606862004855997816982949 5738786625910499590684303)
    ·
      refine ⟨8608179938865749386026455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738786625910499590684303 8608179938865749386026455)
      ·
        refine ⟨12912269908298624079039683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8608179938865749386026455 12912269908298624079039683)
        ·
          refine ⟨19368404862447936118559525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12912269908298624079039683 19368404862447936118559525)
          ·
            refine ⟨3631575911708988022229911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19368404862447936118559525 3631575911708988022229911)
            ·
              refine ⟨5447363867563482033344867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631575911708988022229911 5447363867563482033344867)
              ·
                refine ⟨8171045801345223050017301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5447363867563482033344867 8171045801345223050017301)
                ·
                  refine ⟨383017771938057330469561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8171045801345223050017301 383017771938057330469561)
                  ·
                    rfl

theorem cell20_839165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_839165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839165 prefixEnd_839165 := by exact prefixLift 839165
  have htrace : WordTrace (prefixWord ++ tailWord_839165) baseStart_839165 baseEnd_839165 := by
    simpa [prefixWord, tailWord_839165, baseEnd_839165] using wordTrace_append hprefix tailTrace_839165
  have hstable : (prefixWord ++ tailWord_839165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839165).length < 2 ^ (prefixWord ++ tailWord_839165).sum := by decide
  have hdescent : baseEnd_839165 < baseStart_839165 := by decide
  rcases family_descends (prefixWord ++ tailWord_839165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839188 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 3]
def baseStart_839188 : Nat := 118140960795 + 839188 * 2 ^ 59
def prefixEnd_839188 : Nat := 4983230072969 + 3 ^ 40 * 839188 * 2
def baseEnd_839188 : Nat := 383028269764771472702801

theorem tailTrace_839188 : CollatzResearch.WordTrace tailWord_839188 prefixEnd_839188 383028269764771472702801 := by
  unfold tailWord_839188
  simp only [CollatzResearch.WordTrace]
  refine ⟨15303850441886336372535109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20405133922515115163380145 15303850441886336372535109)
  ·
    refine ⟨2869471957853688069850333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15303850441886336372535109 2869471957853688069850333)
    ·
      refine ⟨1076051984195133026193875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2869471957853688069850333 1076051984195133026193875)
      ·
        refine ⟨1614077976292699539290813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076051984195133026193875 1614077976292699539290813)
        ·
          refine ⟨605279241109762327234055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1614077976292699539290813 605279241109762327234055)
          ·
            refine ⟨907918861664643490851083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605279241109762327234055 907918861664643490851083)
            ·
              refine ⟨1361878292496965236276625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907918861664643490851083 1361878292496965236276625)
              ·
                refine ⟨1021408719372723927207469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361878292496965236276625 1021408719372723927207469)
                ·
                  refine ⟨383028269764771472702801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021408719372723927207469 383028269764771472702801)
                  ·
                    rfl

theorem cell20_839188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_839188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839188 prefixEnd_839188 := by exact prefixLift 839188
  have htrace : WordTrace (prefixWord ++ tailWord_839188) baseStart_839188 baseEnd_839188 := by
    simpa [prefixWord, tailWord_839188, baseEnd_839188] using wordTrace_append hprefix tailTrace_839188
  have hstable : (prefixWord ++ tailWord_839188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839188).length < 2 ^ (prefixWord ++ tailWord_839188).sum := by decide
  have hdescent : baseEnd_839188 < baseStart_839188 := by decide
  rcases family_descends (prefixWord ++ tailWord_839188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839192 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 3]
def baseStart_839192 : Nat := 118140960795 + 839192 * 2 ^ 59
def prefixEnd_839192 : Nat := 4983230072969 + 3 ^ 40 * 839192 * 2
def baseEnd_839192 : Nat := 383030095473765236569451

theorem tailTrace_839192 : CollatzResearch.WordTrace tailWord_839192 prefixEnd_839192 383030095473765236569451 := by
  unfold tailWord_839192
  simp only [CollatzResearch.WordTrace]
  refine ⟨15303923387879090714107915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20405231183838787618810553 15303923387879090714107915)
  ·
    refine ⟨22955885081818636071161873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15303923387879090714107915 22955885081818636071161873)
    ·
      refine ⟨17216913811363977053371405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22955885081818636071161873 17216913811363977053371405)
      ·
        refine ⟨6456342679261491395014277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17216913811363977053371405 6456342679261491395014277)
        ·
          refine ⟨1210564252361529636565177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6456342679261491395014277 1210564252361529636565177)
          ·
            refine ⟨907923189271147227423883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210564252361529636565177 907923189271147227423883)
            ·
              refine ⟨1361884783906720841135825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907923189271147227423883 1361884783906720841135825)
              ·
                refine ⟨1021413587930040630851869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361884783906720841135825 1021413587930040630851869)
                ·
                  refine ⟨383030095473765236569451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021413587930040630851869 383030095473765236569451)
                  ·
                    rfl

theorem cell20_839192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_839192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839192 prefixEnd_839192 := by exact prefixLift 839192
  have htrace : WordTrace (prefixWord ++ tailWord_839192) baseStart_839192 baseEnd_839192 := by
    simpa [prefixWord, tailWord_839192, baseEnd_839192] using wordTrace_append hprefix tailTrace_839192
  have hstable : (prefixWord ++ tailWord_839192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839192).length < 2 ^ (prefixWord ++ tailWord_839192).sum := by decide
  have hdescent : baseEnd_839192 < baseStart_839192 := by decide
  rcases family_descends (prefixWord ++ tailWord_839192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839196 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_839196 : Nat := 118140960795 + 839196 * 2 ^ 59
def prefixEnd_839196 : Nat := 4983230072969 + 3 ^ 40 * 839196 * 2
def baseEnd_839196 : Nat := 383031921182759000436101

theorem tailTrace_839196 : CollatzResearch.WordTrace tailWord_839196 prefixEnd_839196 383031921182759000436101 := by
  unfold tailWord_839196
  simp only [CollatzResearch.WordTrace]
  refine ⟨15303996333871845055680721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20405328445162460074240961 15303996333871845055680721)
  ·
    refine ⟨11477997250403883791760541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15303996333871845055680721 11477997250403883791760541)
    ·
      refine ⟨4304248968901456421910203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11477997250403883791760541 4304248968901456421910203)
      ·
        refine ⟨6456373453352184632865305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304248968901456421910203 6456373453352184632865305)
        ·
          refine ⟨4842280090014138474648979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6456373453352184632865305 4842280090014138474648979)
          ·
            refine ⟨7263420135021207711973469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842280090014138474648979 7263420135021207711973469)
            ·
              refine ⟨2723782550632952891990051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7263420135021207711973469 2723782550632952891990051)
              ·
                refine ⟨4085673825949429337985077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723782550632952891990051 4085673825949429337985077)
                ·
                  refine ⟨383031921182759000436101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4085673825949429337985077 383031921182759000436101)
                  ·
                    rfl

theorem cell20_839196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_839196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839196 prefixEnd_839196 := by exact prefixLift 839196
  have htrace : WordTrace (prefixWord ++ tailWord_839196) baseStart_839196 baseEnd_839196 := by
    simpa [prefixWord, tailWord_839196, baseEnd_839196] using wordTrace_append hprefix tailTrace_839196
  have hstable : (prefixWord ++ tailWord_839196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839196).length < 2 ^ (prefixWord ++ tailWord_839196).sum := by decide
  have hdescent : baseEnd_839196 < baseStart_839196 := by decide
  rcases family_descends (prefixWord ++ tailWord_839196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839258 : List Nat := [3, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_839258 : Nat := 118140960795 + 839258 * 2 ^ 59
def prefixEnd_839258 : Nat := 4983230072969 + 3 ^ 40 * 839258 * 2
def baseEnd_839258 : Nat := 383060219672162340369181

theorem tailTrace_839258 : CollatzResearch.WordTrace tailWord_839258 prefixEnd_839258 383060219672162340369181 := by
  unfold tailWord_839258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7652563498379768675029607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20406835995679383133412285 7652563498379768675029607)
  ·
    refine ⟨11478845247569653012544411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7652563498379768675029607 11478845247569653012544411)
    ·
      refine ⟨17218267871354479518816617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11478845247569653012544411 17218267871354479518816617)
      ·
        refine ⟨12913700903515859639112463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17218267871354479518816617 12913700903515859639112463)
        ·
          refine ⟨19370551355273789458668695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12913700903515859639112463 19370551355273789458668695)
          ·
            refine ⟨29055827032910684188003043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19370551355273789458668695 29055827032910684188003043)
            ·
              refine ⟨43583740549366026282004565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29055827032910684188003043 43583740549366026282004565)
              ·
                refine ⟨510746959562883120492241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 43583740549366026282004565 510746959562883120492241)
                ·
                  refine ⟨383060219672162340369181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510746959562883120492241 383060219672162340369181)
                  ·
                    rfl

theorem cell20_839258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_839258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839258 prefixEnd_839258 := by exact prefixLift 839258
  have htrace : WordTrace (prefixWord ++ tailWord_839258) baseStart_839258 baseEnd_839258 := by
    simpa [prefixWord, tailWord_839258, baseEnd_839258] using wordTrace_append hprefix tailTrace_839258
  have hstable : (prefixWord ++ tailWord_839258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839258).length < 2 ^ (prefixWord ++ tailWord_839258).sum := by decide
  have hdescent : baseEnd_839258 < baseStart_839258 := by decide
  rcases family_descends (prefixWord ++ tailWord_839258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839261 : List Nat := [1, 4, 4, 2, 1, 1, 2, 5]
def baseStart_839261 : Nat := 118140960795 + 839261 * 2 ^ 59
def prefixEnd_839261 : Nat := 4983230072969 + 3 ^ 40 * 839261 * 2
def baseEnd_839261 : Nat := 127687196317969221089723

theorem tailTrace_839261 : CollatzResearch.WordTrace tailWord_839261 prefixEnd_839261 127687196317969221089723 := by
  unfold tailWord_839261
  simp only [CollatzResearch.WordTrace]
  refine ⟨30610363412508206212477637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20406908941672137474985091 30610363412508206212477637)
  ·
    refine ⟨5739443139845288664839557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30610363412508206212477637 5739443139845288664839557)
    ·
      refine ⟨1076145588720991624657417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5739443139845288664839557 1076145588720991624657417)
      ·
        refine ⟨807109191540743718493063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1076145588720991624657417 807109191540743718493063)
        ·
          refine ⟨1210663787311115577739595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807109191540743718493063 1210663787311115577739595)
          ·
            refine ⟨1815995680966673366609393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210663787311115577739595 1815995680966673366609393)
            ·
              refine ⟨1361996760725005024957045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1815995680966673366609393 1361996760725005024957045)
              ·
                refine ⟨127687196317969221089723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1361996760725005024957045 127687196317969221089723)
                ·
                  rfl

theorem cell20_839261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 5].length) (baseStart_839261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839261 prefixEnd_839261 := by exact prefixLift 839261
  have htrace : WordTrace (prefixWord ++ tailWord_839261) baseStart_839261 baseEnd_839261 := by
    simpa [prefixWord, tailWord_839261, baseEnd_839261] using wordTrace_append hprefix tailTrace_839261
  have hstable : (prefixWord ++ tailWord_839261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839261).length < 2 ^ (prefixWord ++ tailWord_839261).sum := by decide
  have hdescent : baseEnd_839261 < baseStart_839261 := by decide
  rcases family_descends (prefixWord ++ tailWord_839261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839268 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 3]
def baseStart_839268 : Nat := 118140960795 + 839268 * 2 ^ 59
def prefixEnd_839268 : Nat := 4983230072969 + 3 ^ 40 * 839268 * 2
def baseEnd_839268 : Nat := 383064783944646750035807

theorem tailTrace_839268 : CollatzResearch.WordTrace tailWord_839268 prefixEnd_839268 383064783944646750035807 := by
  unfold tailWord_839268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15305309361741423203991229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20407079148988564271988305 15305309361741423203991229)
  ·
    refine ⟨5739491010653033701496711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15305309361741423203991229 5739491010653033701496711)
    ·
      refine ⟨8609236515979550552245067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5739491010653033701496711 8609236515979550552245067)
      ·
        refine ⟨12913854773969325828367601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8609236515979550552245067 12913854773969325828367601)
        ·
          refine ⟨9685391080476994371275701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12913854773969325828367601 9685391080476994371275701)
          ·
            refine ⟨908005413794718222307097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9685391080476994371275701 908005413794718222307097)
            ·
              refine ⟨681004060346038666730323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908005413794718222307097 681004060346038666730323)
              ·
                refine ⟨1021506090519058000095485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681004060346038666730323 1021506090519058000095485)
                ·
                  refine ⟨383064783944646750035807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021506090519058000095485 383064783944646750035807)
                  ·
                    rfl

theorem cell20_839268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_839268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839268 prefixEnd_839268 := by exact prefixLift 839268
  have htrace : WordTrace (prefixWord ++ tailWord_839268) baseStart_839268 baseEnd_839268 := by
    simpa [prefixWord, tailWord_839268, baseEnd_839268] using wordTrace_append hprefix tailTrace_839268
  have hstable : (prefixWord ++ tailWord_839268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839268).length < 2 ^ (prefixWord ++ tailWord_839268).sum := by decide
  have hdescent : baseEnd_839268 < baseStart_839268 := by decide
  rcases family_descends (prefixWord ++ tailWord_839268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839296 : List Nat := [2, 1, 1, 2, 1, 4, 2, 5, 2]
def baseStart_839296 : Nat := 118140960795 + 839296 * 2 ^ 59
def prefixEnd_839296 : Nat := 4983230072969 + 3 ^ 40 * 839296 * 2
def baseEnd_839296 : Nat := 383077563907603097102359

theorem tailTrace_839296 : CollatzResearch.WordTrace tailWord_839296 prefixEnd_839296 383077563907603097102359 := by
  unfold tailWord_839296
  simp only [CollatzResearch.WordTrace]
  refine ⟨15305819983690703595000871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20407759978254271460001161 15305819983690703595000871)
  ·
    refine ⟨22958729975536055392501307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15305819983690703595000871 22958729975536055392501307)
    ·
      refine ⟨34438094963304083088751961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22958729975536055392501307 34438094963304083088751961)
      ·
        refine ⟨25828571222478062316563971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34438094963304083088751961 25828571222478062316563971)
        ·
          refine ⟨38742856833717093474845957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25828571222478062316563971 38742856833717093474845957)
          ·
            refine ⟨7264285656321955026533617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38742856833717093474845957 7264285656321955026533617)
            ·
              refine ⟨5448214242241466269900213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7264285656321955026533617 5448214242241466269900213)
              ·
                refine ⟨510770085210137462803145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5448214242241466269900213 510770085210137462803145)
                ·
                  refine ⟨383077563907603097102359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510770085210137462803145 383077563907603097102359)
                  ·
                    rfl

theorem cell20_839296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_839296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839296 prefixEnd_839296 := by exact prefixLift 839296
  have htrace : WordTrace (prefixWord ++ tailWord_839296) baseStart_839296 baseEnd_839296 := by
    simpa [prefixWord, tailWord_839296, baseEnd_839296] using wordTrace_append hprefix tailTrace_839296
  have hstable : (prefixWord ++ tailWord_839296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839296).length < 2 ^ (prefixWord ++ tailWord_839296).sum := by decide
  have hdescent : baseEnd_839296 < baseStart_839296 := by decide
  rcases family_descends (prefixWord ++ tailWord_839296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839351 : List Nat := [1, 1, 3, 1, 5, 2, 2, 3, 2]
def baseStart_839351 : Nat := 118140960795 + 839351 * 2 ^ 59
def prefixEnd_839351 : Nat := 4983230072969 + 3 ^ 40 * 839351 * 2
def baseEnd_839351 : Nat := 383102667406267350268801

theorem tailTrace_839351 : CollatzResearch.WordTrace tailWord_839351 prefixEnd_839351 383102667406267350268801 := by
  unfold tailWord_839351
  simp only [CollatzResearch.WordTrace]
  refine ⟨30613645982182151583253907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20409097321454767722169271 30613645982182151583253907)
  ·
    refine ⟨45920468973273227374880861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30613645982182151583253907 45920468973273227374880861)
    ·
      refine ⟨17220175864977460265580323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45920468973273227374880861 17220175864977460265580323)
      ·
        refine ⟨25830263797466190398370485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17220175864977460265580323 25830263797466190398370485)
        ·
          refine ⟨2421587231012455349847233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25830263797466190398370485 2421587231012455349847233)
          ·
            refine ⟨1816190423259341512385425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2421587231012455349847233 1816190423259341512385425)
            ·
              refine ⟨1362142817444506134289069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1816190423259341512385425 1362142817444506134289069)
              ·
                refine ⟨510803556541689800358401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1362142817444506134289069 510803556541689800358401)
                ·
                  refine ⟨383102667406267350268801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510803556541689800358401 383102667406267350268801)
                  ·
                    rfl

theorem cell20_839351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 2].length) (baseStart_839351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839351 prefixEnd_839351 := by exact prefixLift 839351
  have htrace : WordTrace (prefixWord ++ tailWord_839351) baseStart_839351 baseEnd_839351 := by
    simpa [prefixWord, tailWord_839351, baseEnd_839351] using wordTrace_append hprefix tailTrace_839351
  have hstable : (prefixWord ++ tailWord_839351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839351).length < 2 ^ (prefixWord ++ tailWord_839351).sum := by decide
  have hdescent : baseEnd_839351 < baseStart_839351 := by decide
  rcases family_descends (prefixWord ++ tailWord_839351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839407 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_839407 : Nat := 118140960795 + 839407 * 2 ^ 59
def prefixEnd_839407 : Nat := 4983230072969 + 3 ^ 40 * 839407 * 2
def baseEnd_839407 : Nat := 383128227332180044401905

theorem tailTrace_839407 : CollatzResearch.WordTrace tailWord_839407 prefixEnd_839407 383128227332180044401905 := by
  unfold tailWord_839407
  simp only [CollatzResearch.WordTrace]
  refine ⟨30615688469979273147292475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20410458979986182098194983 30615688469979273147292475)
  ·
    refine ⟨45923532704968909720938713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30615688469979273147292475 45923532704968909720938713)
    ·
      refine ⟨34442649528726682290704035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45923532704968909720938713 34442649528726682290704035)
      ·
        refine ⟨51663974293090023436056053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34442649528726682290704035 51663974293090023436056053)
        ·
          refine ⟨4843497589977189697130255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51663974293090023436056053 4843497589977189697130255)
          ·
            refine ⟨7265246384965784545695383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843497589977189697130255 7265246384965784545695383)
            ·
              refine ⟨10897869577448676818543075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265246384965784545695383 10897869577448676818543075)
              ·
                refine ⟨16346804366173015227814613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10897869577448676818543075 16346804366173015227814613)
                ·
                  refine ⟨383128227332180044401905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16346804366173015227814613 383128227332180044401905)
                  ·
                    rfl

theorem cell20_839407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_839407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839407 prefixEnd_839407 := by exact prefixLift 839407
  have htrace : WordTrace (prefixWord ++ tailWord_839407) baseStart_839407 baseEnd_839407 := by
    simpa [prefixWord, tailWord_839407, baseEnd_839407] using wordTrace_append hprefix tailTrace_839407
  have hstable : (prefixWord ++ tailWord_839407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839407).length < 2 ^ (prefixWord ++ tailWord_839407).sum := by decide
  have hdescent : baseEnd_839407 < baseStart_839407 := by decide
  rcases family_descends (prefixWord ++ tailWord_839407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839438 : List Nat := [4, 1, 1, 2, 1, 1, 3, 7]
def baseStart_839438 : Nat := 118140960795 + 839438 * 2 ^ 59
def prefixEnd_839438 : Nat := 4983230072969 + 3 ^ 40 * 839438 * 2
def baseEnd_839438 : Nat := 127714125525627238122815

theorem tailTrace_839438 : CollatzResearch.WordTrace tailWord_839438 prefixEnd_839438 127714125525627238122815 := by
  unfold tailWord_839438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827102391608370680208871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20411212755244643627780645 3827102391608370680208871)
  ·
    refine ⟨5740653587412556020313307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3827102391608370680208871 5740653587412556020313307)
    ·
      refine ⟨8610980381118834030469961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5740653587412556020313307 8610980381118834030469961)
      ·
        refine ⟨6458235285839125522852471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8610980381118834030469961 6458235285839125522852471)
        ·
          refine ⟨9687352928758688284278707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6458235285839125522852471 9687352928758688284278707)
          ·
            refine ⟨14531029393138032426418061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9687352928758688284278707 14531029393138032426418061)
            ·
              refine ⟨5449136022426762159906773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14531029393138032426418061 5449136022426762159906773)
              ·
                refine ⟨127714125525627238122815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5449136022426762159906773 127714125525627238122815)
                ·
                  rfl

theorem cell20_839438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_839438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839438 prefixEnd_839438 := by exact prefixLift 839438
  have htrace : WordTrace (prefixWord ++ tailWord_839438) baseStart_839438 baseEnd_839438 := by
    simpa [prefixWord, tailWord_839438, baseEnd_839438] using wordTrace_append hprefix tailTrace_839438
  have hstable : (prefixWord ++ tailWord_839438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839438).length < 2 ^ (prefixWord ++ tailWord_839438).sum := by decide
  have hdescent : baseEnd_839438 < baseStart_839438 := by decide
  rcases family_descends (prefixWord ++ tailWord_839438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839482 : List Nat := [3, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_839482 : Nat := 118140960795 + 839482 * 2 ^ 59
def prefixEnd_839482 : Nat := 4983230072969 + 3 ^ 40 * 839482 * 2
def baseEnd_839482 : Nat := 383162459375813116901599

theorem tailTrace_839482 : CollatzResearch.WordTrace tailWord_839482 prefixEnd_839482 383162459375813116901599 := by
  unfold tailWord_839482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654605986176890239068175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20412282629805040637515133 7654605986176890239068175)
  ·
    refine ⟨11481908979265335358602263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7654605986176890239068175 11481908979265335358602263)
    ·
      refine ⟨17222863468898003037903395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11481908979265335358602263 17222863468898003037903395)
      ·
        refine ⟨25834295203347004556855093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17222863468898003037903395 25834295203347004556855093)
        ·
          refine ⟨2421965175313781677205165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25834295203347004556855093 2421965175313781677205165)
          ·
            refine ⟨908236940742668128951937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2421965175313781677205165 908236940742668128951937)
            ·
              refine ⟨681177705557001096713953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908236940742668128951937 681177705557001096713953)
              ·
                refine ⟨510883279167750822535465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681177705557001096713953 510883279167750822535465)
                ·
                  refine ⟨383162459375813116901599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510883279167750822535465 383162459375813116901599)
                  ·
                    rfl

theorem cell20_839482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_839482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839482 prefixEnd_839482 := by exact prefixLift 839482
  have htrace : WordTrace (prefixWord ++ tailWord_839482) baseStart_839482 baseEnd_839482 := by
    simpa [prefixWord, tailWord_839482, baseEnd_839482] using wordTrace_append hprefix tailTrace_839482
  have hstable : (prefixWord ++ tailWord_839482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839482).length < 2 ^ (prefixWord ++ tailWord_839482).sum := by decide
  have hdescent : baseEnd_839482 < baseStart_839482 := by decide
  rcases family_descends (prefixWord ++ tailWord_839482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839521 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_839521 : Nat := 118140960795 + 839521 * 2 ^ 59
def prefixEnd_839521 : Nat := 4983230072969 + 3 ^ 40 * 839521 * 2
def baseEnd_839521 : Nat := 383180260038502314601439

theorem tailTrace_839521 : CollatzResearch.WordTrace tailWord_839521 prefixEnd_839521 383180260038502314601439 := by
  unfold tailWord_839521
  simp only [CollatzResearch.WordTrace]
  refine ⟨30619846391566270616942417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20413230927710847077961611 30619846391566270616942417)
  ·
    refine ⟨22964884793674702962706813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30619846391566270616942417 22964884793674702962706813)
    ·
      refine ⟨8611831797628013611015055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22964884793674702962706813 8611831797628013611015055)
      ·
        refine ⟨12917747696442020416522583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8611831797628013611015055 12917747696442020416522583)
        ·
          refine ⟨19376621544663030624783875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12917747696442020416522583 19376621544663030624783875)
          ·
            refine ⟨29064932316994545937175813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19376621544663030624783875 29064932316994545937175813)
            ·
              refine ⟨5449674809436477363220465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29064932316994545937175813 5449674809436477363220465)
              ·
                refine ⟨4087256107077358022415349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5449674809436477363220465 4087256107077358022415349)
                ·
                  refine ⟨383180260038502314601439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4087256107077358022415349 383180260038502314601439)
                  ·
                    rfl

theorem cell20_839521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_839521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839521 prefixEnd_839521 := by exact prefixLift 839521
  have htrace : WordTrace (prefixWord ++ tailWord_839521) baseStart_839521 baseEnd_839521 := by
    simpa [prefixWord, tailWord_839521, baseEnd_839521] using wordTrace_append hprefix tailTrace_839521
  have hstable : (prefixWord ++ tailWord_839521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839521).length < 2 ^ (prefixWord ++ tailWord_839521).sum := by decide
  have hdescent : baseEnd_839521 < baseStart_839521 := by decide
  rcases family_descends (prefixWord ++ tailWord_839521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839534 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_839534 : Nat := 118140960795 + 839534 * 2 ^ 59
def prefixEnd_839534 : Nat := 4983230072969 + 3 ^ 40 * 839534 * 2
def baseEnd_839534 : Nat := 383186193592732047168053

theorem tailTrace_839534 : CollatzResearch.WordTrace tailWord_839534 prefixEnd_839534 383186193592732047168053 := by
  unfold tailWord_839534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827540067564896729645707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20413547027012782558110437 3827540067564896729645707)
  ·
    refine ⟨5741310101347345094468561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3827540067564896729645707 5741310101347345094468561)
    ·
      refine ⟨4305982576010508820851421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5741310101347345094468561 4305982576010508820851421)
      ·
        refine ⟨1614743466003940807819283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4305982576010508820851421 1614743466003940807819283)
        ·
          refine ⟨2422115199005911211728925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1614743466003940807819283 2422115199005911211728925)
          ·
            refine ⟨908293199627216704398347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2422115199005911211728925 908293199627216704398347)
            ·
              refine ⟨1362439799440825056597521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908293199627216704398347 1362439799440825056597521)
              ·
                refine ⟨1021829849580618792448141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362439799440825056597521 1021829849580618792448141)
                ·
                  refine ⟨383186193592732047168053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021829849580618792448141 383186193592732047168053)
                  ·
                    rfl

theorem cell20_839534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_839534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839534 prefixEnd_839534 := by exact prefixLift 839534
  have htrace : WordTrace (prefixWord ++ tailWord_839534) baseStart_839534 baseEnd_839534 := by
    simpa [prefixWord, tailWord_839534, baseEnd_839534] using wordTrace_append hprefix tailTrace_839534
  have hstable : (prefixWord ++ tailWord_839534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839534).length < 2 ^ (prefixWord ++ tailWord_839534).sum := by decide
  have hdescent : baseEnd_839534 < baseStart_839534 := by decide
  rcases family_descends (prefixWord ++ tailWord_839534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839545 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 4]
def baseStart_839545 : Nat := 118140960795 + 839545 * 2 ^ 59
def prefixEnd_839545 : Nat := 4983230072969 + 3 ^ 40 * 839545 * 2
def baseEnd_839545 : Nat := 383191214292464897801341

theorem tailTrace_839545 : CollatzResearch.WordTrace tailWord_839545 prefixEnd_839545 383191214292464897801341 := by
  unfold tailWord_839545
  simp only [CollatzResearch.WordTrace]
  refine ⟨30620721743479322715816089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20413814495652881810544059 30620721743479322715816089)
  ·
    refine ⟨22965541307609492036862067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30620721743479322715816089 22965541307609492036862067)
    ·
      refine ⟨34448311961414238055293101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22965541307609492036862067 34448311961414238055293101)
      ·
        refine ⟨12918116985530339270734913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34448311961414238055293101 12918116985530339270734913)
        ·
          refine ⟨9688587739147754453051185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12918116985530339270734913 9688587739147754453051185)
          ·
            refine ⟨7266440804360815839788389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9688587739147754453051185 7266440804360815839788389)
            ·
              refine ⟨1362457650817652969960323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7266440804360815839788389 1362457650817652969960323)
              ·
                refine ⟨2043686476226479454940485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362457650817652969960323 2043686476226479454940485)
                ·
                  refine ⟨383191214292464897801341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2043686476226479454940485 383191214292464897801341)
                  ·
                    rfl

theorem cell20_839545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_839545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839545 prefixEnd_839545 := by exact prefixLift 839545
  have htrace : WordTrace (prefixWord ++ tailWord_839545) baseStart_839545 baseEnd_839545 := by
    simpa [prefixWord, tailWord_839545, baseEnd_839545] using wordTrace_append hprefix tailTrace_839545
  have hstable : (prefixWord ++ tailWord_839545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839545).length < 2 ^ (prefixWord ++ tailWord_839545).sum := by decide
  have hdescent : baseEnd_839545 < baseStart_839545 := by decide
  rcases family_descends (prefixWord ++ tailWord_839545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839555 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 3]
def baseStart_839555 : Nat := 118140960795 + 839555 * 2 ^ 59
def prefixEnd_839555 : Nat := 4983230072969 + 3 ^ 40 * 839555 * 2
def baseEnd_839555 : Nat := 383195778564949307467967

theorem tailTrace_839555 : CollatzResearch.WordTrace tailWord_839555 prefixEnd_839555 383195778564949307467967 := by
  unfold tailWord_839555
  simp only [CollatzResearch.WordTrace]
  refine ⟨30621086473443094423680119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20414057648962062949120079 30621086473443094423680119)
  ·
    refine ⟨45931629710164641635520179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30621086473443094423680119 45931629710164641635520179)
    ·
      refine ⟨68897444565246962453280269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45931629710164641635520179 68897444565246962453280269)
      ·
        refine ⟨25836541711967610919980101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68897444565246962453280269 25836541711967610919980101)
        ·
          refine ⟨4844351570993927047496269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25836541711967610919980101 4844351570993927047496269)
          ·
            refine ⟨1816631839122722642811101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4844351570993927047496269 1816631839122722642811101)
            ·
              refine ⟨681236939671020991054163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1816631839122722642811101 681236939671020991054163)
              ·
                refine ⟨1021855409506531486581245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681236939671020991054163 1021855409506531486581245)
                ·
                  refine ⟨383195778564949307467967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021855409506531486581245 383195778564949307467967)
                  ·
                    rfl

theorem cell20_839555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 3].length) (baseStart_839555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839555 prefixEnd_839555 := by exact prefixLift 839555
  have htrace : WordTrace (prefixWord ++ tailWord_839555) baseStart_839555 baseEnd_839555 := by
    simpa [prefixWord, tailWord_839555, baseEnd_839555] using wordTrace_append hprefix tailTrace_839555
  have hstable : (prefixWord ++ tailWord_839555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839555).length < 2 ^ (prefixWord ++ tailWord_839555).sum := by decide
  have hdescent : baseEnd_839555 < baseStart_839555 := by decide
  rcases family_descends (prefixWord ++ tailWord_839555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839586 : List Nat := [3, 3, 1, 2, 4, 1, 6]
def baseStart_839586 : Nat := 118140960795 + 839586 * 2 ^ 59
def prefixEnd_839586 : Nat := 4983230072969 + 3 ^ 40 * 839586 * 2
def baseEnd_839586 : Nat := 42578880867738997492723

theorem tailTrace_839586 : CollatzResearch.WordTrace tailWord_839586 prefixEnd_839586 42578880867738997492723 := by
  unfold tailWord_839586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7655554284082696679514653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20414811424220524478705741 7655554284082696679514653)
  ·
    refine ⟨2870832856531011254817995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7655554284082696679514653 2870832856531011254817995)
    ·
      refine ⟨4306249284796516882226993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2870832856531011254817995 4306249284796516882226993)
      ·
        refine ⟨3229686963597387661670245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4306249284796516882226993 3229686963597387661670245)
        ·
          refine ⟨605566305674510186563171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3229686963597387661670245 605566305674510186563171)
          ·
            refine ⟨908349458511765279844757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605566305674510186563171 908349458511765279844757)
            ·
              refine ⟨42578880867738997492723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 908349458511765279844757 42578880867738997492723)
              ·
                rfl

theorem cell20_839586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 6].length) (baseStart_839586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839586 prefixEnd_839586 := by exact prefixLift 839586
  have htrace : WordTrace (prefixWord ++ tailWord_839586) baseStart_839586 baseEnd_839586 := by
    simpa [prefixWord, tailWord_839586, baseEnd_839586] using wordTrace_append hprefix tailTrace_839586
  have hstable : (prefixWord ++ tailWord_839586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839586).length < 2 ^ (prefixWord ++ tailWord_839586).sum := by decide
  have hdescent : baseEnd_839586 < baseStart_839586 := by decide
  rcases family_descends (prefixWord ++ tailWord_839586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839611 : List Nat := [1, 1, 1, 1, 1, 2, 2, 11]
def baseStart_839611 : Nat := 118140960795 + 839611 * 2 ^ 59
def prefixEnd_839611 : Nat := 4983230072969 + 3 ^ 40 * 839611 * 2
def baseEnd_839611 : Nat := 127740446163620667200357

theorem tailTrace_839611 : CollatzResearch.WordTrace tailWord_839611 prefixEnd_839611 127740446163620667200357 := by
  unfold tailWord_839611
  simp only [CollatzResearch.WordTrace]
  refine ⟨30623128961240215987718687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20415419307493477325145791 30623128961240215987718687)
  ·
    refine ⟨45934693441860323981578031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30623128961240215987718687 45934693441860323981578031)
    ·
      refine ⟨68902040162790485972367047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45934693441860323981578031 68902040162790485972367047)
      ·
        refine ⟨103353060244185728958550571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68902040162790485972367047 103353060244185728958550571)
        ·
          refine ⟨155029590366278593437825857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103353060244185728958550571 155029590366278593437825857)
          ·
            refine ⟨116272192774708945078369393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155029590366278593437825857 116272192774708945078369393)
            ·
              refine ⟨87204144581031708808777045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116272192774708945078369393 87204144581031708808777045)
              ·
                refine ⟨127740446163620667200357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 87204144581031708808777045 127740446163620667200357)
                ·
                  rfl

theorem cell20_839611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_839611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839611 prefixEnd_839611 := by exact prefixLift 839611
  have htrace : WordTrace (prefixWord ++ tailWord_839611) baseStart_839611 baseEnd_839611 := by
    simpa [prefixWord, tailWord_839611, baseEnd_839611] using wordTrace_append hprefix tailTrace_839611
  have hstable : (prefixWord ++ tailWord_839611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839611).length < 2 ^ (prefixWord ++ tailWord_839611).sum := by decide
  have hdescent : baseEnd_839611 < baseStart_839611 := by decide
  rcases family_descends (prefixWord ++ tailWord_839611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839628 : List Nat := [2, 2, 1, 4, 1, 2, 2, 6]
def baseStart_839628 : Nat := 118140960795 + 839628 * 2 ^ 59
def prefixEnd_839628 : Nat := 4983230072969 + 3 ^ 40 * 839628 * 2
def baseEnd_839628 : Nat := 127743032584695166011445

theorem tailTrace_839628 : CollatzResearch.WordTrace tailWord_839628 prefixEnd_839628 127743032584695166011445 := by
  unfold tailWord_839628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15311874501089313945543769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20415832668119085260725025 15311874501089313945543769)
  ·
    refine ⟨11483905875816985459157827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15311874501089313945543769 11483905875816985459157827)
    ·
      refine ⟨17225858813725478188736741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11483905875816985459157827 17225858813725478188736741)
      ·
        refine ⟨3229848527573527160388139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17225858813725478188736741 3229848527573527160388139)
        ·
          refine ⟨4844772791360290740582209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229848527573527160388139 4844772791360290740582209)
          ·
            refine ⟨3633579593520218055436657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4844772791360290740582209 3633579593520218055436657)
            ·
              refine ⟨2725184695140163541577493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3633579593520218055436657 2725184695140163541577493)
              ·
                refine ⟨127743032584695166011445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2725184695140163541577493 127743032584695166011445)
                ·
                  rfl

theorem cell20_839628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_839628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839628 prefixEnd_839628 := by exact prefixLift 839628
  have htrace : WordTrace (prefixWord ++ tailWord_839628) baseStart_839628 baseEnd_839628 := by
    simpa [prefixWord, tailWord_839628, baseEnd_839628] using wordTrace_append hprefix tailTrace_839628
  have hstable : (prefixWord ++ tailWord_839628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839628).length < 2 ^ (prefixWord ++ tailWord_839628).sum := by decide
  have hdescent : baseEnd_839628 < baseStart_839628 := by decide
  rcases family_descends (prefixWord ++ tailWord_839628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839645 : List Nat := [1, 4, 3, 1, 4, 7]
def baseStart_839645 : Nat := 118140960795 + 839645 * 2 ^ 59
def prefixEnd_839645 : Nat := 4983230072969 + 3 ^ 40 * 839645 * 2
def baseEnd_839645 : Nat := 14193957667307740535837

theorem tailTrace_839645 : CollatzResearch.WordTrace tailWord_839645 prefixEnd_839645 14193957667307740535837 := by
  unfold tailWord_839645
  simp only [CollatzResearch.WordTrace]
  refine ⟨30624369043117039794456389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20416246028744693196304259 30624369043117039794456389)
  ·
    refine ⟨5742069195584444961460573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30624369043117039794456389 5742069195584444961460573)
    ·
      refine ⟨2153275948344166860547715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5742069195584444961460573 2153275948344166860547715)
      ·
        refine ⟨3229913922516250290821573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153275948344166860547715 3229913922516250290821573)
        ·
          refine ⟨605608860471796929529045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3229913922516250290821573 605608860471796929529045)
          ·
            refine ⟨14193957667307740535837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 605608860471796929529045 14193957667307740535837)
            ·
              rfl

theorem cell20_839645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 7].length) (baseStart_839645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839645 prefixEnd_839645 := by exact prefixLift 839645
  have htrace : WordTrace (prefixWord ++ tailWord_839645) baseStart_839645 baseEnd_839645 := by
    simpa [prefixWord, tailWord_839645, baseEnd_839645] using wordTrace_append hprefix tailTrace_839645
  have hstable : (prefixWord ++ tailWord_839645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839645).length < 2 ^ (prefixWord ++ tailWord_839645).sum := by decide
  have hdescent : baseEnd_839645 < baseStart_839645 := by decide
  rcases family_descends (prefixWord ++ tailWord_839645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839652 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_839652 : Nat := 118140960795 + 839652 * 2 ^ 59
def prefixEnd_839652 : Nat := 4983230072969 + 3 ^ 40 * 839652 * 2
def baseEnd_839652 : Nat := 383240052008048081234237

theorem tailTrace_839652 : CollatzResearch.WordTrace tailWord_839652 prefixEnd_839652 383240052008048081234237 := by
  unfold tailWord_839652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15312312177045839994980605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20416416236061119993307473 15312312177045839994980605)
  ·
    refine ⟨5742117066392189998117727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15312312177045839994980605 5742117066392189998117727)
    ·
      refine ⟨8613175599588284997176591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5742117066392189998117727 8613175599588284997176591)
      ·
        refine ⟨12919763399382427495764887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8613175599588284997176591 12919763399382427495764887)
        ·
          refine ⟨19379645099073641243647331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12919763399382427495764887 19379645099073641243647331)
          ·
            refine ⟨29069467648610461865470997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19379645099073641243647331 29069467648610461865470997)
            ·
              refine ⟨1362631296028615399943953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29069467648610461865470997 1362631296028615399943953)
              ·
                refine ⟨1021973472021461549957965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362631296028615399943953 1021973472021461549957965)
                ·
                  refine ⟨383240052008048081234237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021973472021461549957965 383240052008048081234237)
                  ·
                    rfl

theorem cell20_839652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_839652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839652 prefixEnd_839652 := by exact prefixLift 839652
  have htrace : WordTrace (prefixWord ++ tailWord_839652) baseStart_839652 baseEnd_839652 := by
    simpa [prefixWord, tailWord_839652, baseEnd_839652] using wordTrace_append hprefix tailTrace_839652
  have hstable : (prefixWord ++ tailWord_839652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839652).length < 2 ^ (prefixWord ++ tailWord_839652).sum := by decide
  have hdescent : baseEnd_839652 < baseStart_839652 := by decide
  rcases family_descends (prefixWord ++ tailWord_839652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839655 : List Nat := [1, 1, 5, 2, 3, 1, 1, 4, 2]
def baseStart_839655 : Nat := 118140960795 + 839655 * 2 ^ 59
def prefixEnd_839655 : Nat := 4983230072969 + 3 ^ 40 * 839655 * 2
def baseEnd_839655 : Nat := 383241421289793404134225

theorem tailTrace_839655 : CollatzResearch.WordTrace tailWord_839655 prefixEnd_839655 383241421289793404134225 := by
  unfold tailWord_839655
  simp only [CollatzResearch.WordTrace]
  refine ⟨30624733773080811502320419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20416489182053874334880279 30624733773080811502320419)
  ·
    refine ⟨45937100659621217253480629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30624733773080811502320419 45937100659621217253480629)
    ·
      refine ⟨4306603186839489117513809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45937100659621217253480629 4306603186839489117513809)
      ·
        refine ⟨3229952390129616838135357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4306603186839489117513809 3229952390129616838135357)
        ·
          refine ⟨1211232146298606314300759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3229952390129616838135357 1211232146298606314300759)
          ·
            refine ⟨1816848219447909471451139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211232146298606314300759 1816848219447909471451139)
            ·
              refine ⟨2725272329171864207176709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816848219447909471451139 2725272329171864207176709)
              ·
                refine ⟨510988561719724538845633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2725272329171864207176709 510988561719724538845633)
                ·
                  refine ⟨383241421289793404134225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510988561719724538845633 383241421289793404134225)
                  ·
                    rfl

theorem cell20_839655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 2].length) (baseStart_839655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839655 prefixEnd_839655 := by exact prefixLift 839655
  have htrace : WordTrace (prefixWord ++ tailWord_839655) baseStart_839655 baseEnd_839655 := by
    simpa [prefixWord, tailWord_839655, baseEnd_839655] using wordTrace_append hprefix tailTrace_839655
  have hstable : (prefixWord ++ tailWord_839655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839655).length < 2 ^ (prefixWord ++ tailWord_839655).sum := by decide
  have hdescent : baseEnd_839655 < baseStart_839655 := by decide
  rcases family_descends (prefixWord ++ tailWord_839655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839700 : List Nat := [2, 4, 3, 2, 1, 1, 7]
def baseStart_839700 : Nat := 118140960795 + 839700 * 2 ^ 59
def prefixEnd_839700 : Nat := 4983230072969 + 3 ^ 40 * 839700 * 2
def baseEnd_839700 : Nat := 42584662279552583070449

theorem tailTrace_839700 : CollatzResearch.WordTrace tailWord_839700 prefixEnd_839700 42584662279552583070449 := by
  unfold tailWord_839700
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313187528958892093854277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20417583371945189458472369 15313187528958892093854277)
  ·
    refine ⟨2871222661679792267597677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15313187528958892093854277 2871222661679792267597677)
    ·
      refine ⟨1076708498129922100349129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2871222661679792267597677 1076708498129922100349129)
      ·
        refine ⟨807531373597441575261847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1076708498129922100349129 807531373597441575261847)
        ·
          refine ⟨1211297060396162362892771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807531373597441575261847 1211297060396162362892771)
          ·
            refine ⟨1816945590594243544339157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211297060396162362892771 1816945590594243544339157)
            ·
              refine ⟨42584662279552583070449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1816945590594243544339157 42584662279552583070449)
              ·
                rfl

theorem cell20_839700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 7].length) (baseStart_839700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839700 prefixEnd_839700 := by exact prefixLift 839700
  have htrace : WordTrace (prefixWord ++ tailWord_839700) baseStart_839700 baseEnd_839700 := by
    simpa [prefixWord, tailWord_839700, baseEnd_839700] using wordTrace_append hprefix tailTrace_839700
  have hstable : (prefixWord ++ tailWord_839700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839700).length < 2 ^ (prefixWord ++ tailWord_839700).sum := by decide
  have hdescent : baseEnd_839700 < baseStart_839700 := by decide
  rcases family_descends (prefixWord ++ tailWord_839700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839711 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 5]
def baseStart_839711 : Nat := 118140960795 + 839711 * 2 ^ 59
def prefixEnd_839711 : Nat := 4983230072969 + 3 ^ 40 * 839711 * 2
def baseEnd_839711 : Nat := 383266981215706098267329

theorem tailTrace_839711 : CollatzResearch.WordTrace tailWord_839711 prefixEnd_839711 383266981215706098267329 := by
  unfold tailWord_839711
  simp only [CollatzResearch.WordTrace]
  refine ⟨30626776260877933066358987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20417850840585288710905991 30626776260877933066358987)
  ·
    refine ⟨45940164391316899599538481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30626776260877933066358987 45940164391316899599538481)
    ·
      refine ⟨34455123293487674699653861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45940164391316899599538481 34455123293487674699653861)
      ·
        refine ⟨6460335617528939006185099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34455123293487674699653861 6460335617528939006185099)
        ·
          refine ⟨9690503426293408509277649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460335617528939006185099 9690503426293408509277649)
          ·
            refine ⟨7267877569720056381958237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9690503426293408509277649 7267877569720056381958237)
            ·
              refine ⟨2725454088645021143234339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7267877569720056381958237 2725454088645021143234339)
              ·
                refine ⟨4088181132967531714851509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725454088645021143234339 4088181132967531714851509)
                ·
                  refine ⟨383266981215706098267329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4088181132967531714851509 383266981215706098267329)
                  ·
                    rfl

theorem cell20_839711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_839711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839711 prefixEnd_839711 := by exact prefixLift 839711
  have htrace : WordTrace (prefixWord ++ tailWord_839711) baseStart_839711 baseEnd_839711 := by
    simpa [prefixWord, tailWord_839711, baseEnd_839711] using wordTrace_append hprefix tailTrace_839711
  have hstable : (prefixWord ++ tailWord_839711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839711).length < 2 ^ (prefixWord ++ tailWord_839711).sum := by decide
  have hdescent : baseEnd_839711 < baseStart_839711 := by decide
  rcases family_descends (prefixWord ++ tailWord_839711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839714 : List Nat := [3, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_839714 : Nat := 118140960795 + 839714 * 2 ^ 59
def prefixEnd_839714 : Nat := 4983230072969 + 3 ^ 40 * 839714 * 2
def baseEnd_839714 : Nat := 383268350497451421167317

theorem tailTrace_839714 : CollatzResearch.WordTrace tailWord_839714 prefixEnd_839714 383268350497451421167317 := by
  unfold tailWord_839714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7656721419966766144679549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20417923786578043052478797 7656721419966766144679549)
  ·
    refine ⟨2871270532487537304254831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7656721419966766144679549 2871270532487537304254831)
    ·
      refine ⟨4306905798731305956382247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2871270532487537304254831 4306905798731305956382247)
      ·
        refine ⟨6460358698096958934573371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306905798731305956382247 6460358698096958934573371)
        ·
          refine ⟨9690538047145438401860057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460358698096958934573371 9690538047145438401860057)
          ·
            refine ⟨7267903535359078801395043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9690538047145438401860057 7267903535359078801395043)
            ·
              refine ⟨10901855303038618202092565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7267903535359078801395043 10901855303038618202092565)
              ·
                refine ⟨511024467329935228223089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10901855303038618202092565 511024467329935228223089)
                ·
                  refine ⟨383268350497451421167317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511024467329935228223089 383268350497451421167317)
                  ·
                    rfl

theorem cell20_839714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_839714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839714 prefixEnd_839714 := by exact prefixLift 839714
  have htrace : WordTrace (prefixWord ++ tailWord_839714) baseStart_839714 baseEnd_839714 := by
    simpa [prefixWord, tailWord_839714, baseEnd_839714] using wordTrace_append hprefix tailTrace_839714
  have hstable : (prefixWord ++ tailWord_839714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839714).length < 2 ^ (prefixWord ++ tailWord_839714).sum := by decide
  have hdescent : baseEnd_839714 < baseStart_839714 := by decide
  rcases family_descends (prefixWord ++ tailWord_839714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839756 : List Nat := [2, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_839756 : Nat := 118140960795 + 839756 * 2 ^ 59
def prefixEnd_839756 : Nat := 4983230072969 + 3 ^ 40 * 839756 * 2
def baseEnd_839756 : Nat := 383287520441885941767145

theorem tailTrace_839756 : CollatzResearch.WordTrace tailWord_839756 prefixEnd_839756 383287520441885941767145 := by
  unfold tailWord_839756
  simp only [CollatzResearch.WordTrace]
  refine ⟨15314208772857452875873561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20418945030476603834498081 15314208772857452875873561)
  ·
    refine ⟨11485656579643089656905171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15314208772857452875873561 11485656579643089656905171)
    ·
      refine ⟨17228484869464634485357757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11485656579643089656905171 17228484869464634485357757)
      ·
        refine ⟨6460681826049237932009159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17228484869464634485357757 6460681826049237932009159)
        ·
          refine ⟨9691022739073856898013739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460681826049237932009159 9691022739073856898013739)
          ·
            refine ⟨14536534108610785347020609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9691022739073856898013739 14536534108610785347020609)
            ·
              refine ⟨10902400581458089010265457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14536534108610785347020609 10902400581458089010265457)
              ·
                refine ⟨8176800436093566757699093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10902400581458089010265457 8176800436093566757699093)
                ·
                  refine ⟨383287520441885941767145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8176800436093566757699093 383287520441885941767145)
                  ·
                    rfl

theorem cell20_839756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_839756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839756 prefixEnd_839756 := by exact prefixLift 839756
  have htrace : WordTrace (prefixWord ++ tailWord_839756) baseStart_839756 baseEnd_839756 := by
    simpa [prefixWord, tailWord_839756, baseEnd_839756] using wordTrace_append hprefix tailTrace_839756
  have hstable : (prefixWord ++ tailWord_839756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839756).length < 2 ^ (prefixWord ++ tailWord_839756).sum := by decide
  have hdescent : baseEnd_839756 < baseStart_839756 := by decide
  rcases family_descends (prefixWord ++ tailWord_839756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839873 : List Nat := [1, 2, 6, 1, 2, 1, 7]
def baseStart_839873 : Nat := 118140960795 + 839873 * 2 ^ 59
def prefixEnd_839873 : Nat := 4983230072969 + 3 ^ 40 * 839873 * 2
def baseEnd_839873 : Nat := 42593435825550392762963

theorem tailTrace_839873 : CollatzResearch.WordTrace tailWord_839873 prefixEnd_839873 42593435825550392762963 := by
  unfold tailWord_839873
  simp only [CollatzResearch.WordTrace]
  refine ⟨30632684886291034733756273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20421789924194023155837515 30632684886291034733756273)
  ·
    refine ⟨22974513664718276050317205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30632684886291034733756273 22974513664718276050317205)
    ·
      refine ⟨1076930328033669189858619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22974513664718276050317205 1076930328033669189858619)
      ·
        refine ⟨1615395492050503784787929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076930328033669189858619 1615395492050503784787929)
        ·
          refine ⟨1211546619037877838590947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615395492050503784787929 1211546619037877838590947)
          ·
            refine ⟨1817319928556816757886421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211546619037877838590947 1817319928556816757886421)
            ·
              refine ⟨42593435825550392762963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1817319928556816757886421 42593435825550392762963)
              ·
                rfl

theorem cell20_839873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 7].length) (baseStart_839873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839873 prefixEnd_839873 := by exact prefixLift 839873
  have htrace : WordTrace (prefixWord ++ tailWord_839873) baseStart_839873 baseEnd_839873 := by
    simpa [prefixWord, tailWord_839873, baseEnd_839873] using wordTrace_append hprefix tailTrace_839873
  have hstable : (prefixWord ++ tailWord_839873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839873).length < 2 ^ (prefixWord ++ tailWord_839873).sum := by decide
  have hdescent : baseEnd_839873 < baseStart_839873 := by decide
  rcases family_descends (prefixWord ++ tailWord_839873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839887 : List Nat := [1, 1, 2, 1, 1, 3, 3, 6, 2]
def baseStart_839887 : Nat := 118140960795 + 839887 * 2 ^ 59
def prefixEnd_839887 : Nat := 4983230072969 + 3 ^ 40 * 839887 * 2
def baseEnd_839887 : Nat := 383347312411431708399943

theorem tailTrace_839887 : CollatzResearch.WordTrace tailWord_839887 prefixEnd_839887 383347312411431708399943 := by
  unfold tailWord_839887
  simp only [CollatzResearch.WordTrace]
  refine ⟨30633195508240315124765915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20422130338826876749843943 30633195508240315124765915)
  ·
    refine ⟨45949793262360472687148873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30633195508240315124765915 45949793262360472687148873)
    ·
      refine ⟨34462344946770354515361655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45949793262360472687148873 34462344946770354515361655)
      ·
        refine ⟨51693517420155531773042483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34462344946770354515361655 51693517420155531773042483)
        ·
          refine ⟨77540276130233297659563725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51693517420155531773042483 77540276130233297659563725)
          ·
            refine ⟨29077603548837486622336397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77540276130233297659563725 29077603548837486622336397)
            ·
              refine ⟨10904101330814057483376149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29077603548837486622336397 10904101330814057483376149)
              ·
                refine ⟨511129749881908944533257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10904101330814057483376149 511129749881908944533257)
                ·
                  refine ⟨383347312411431708399943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511129749881908944533257 383347312411431708399943)
                  ·
                    rfl

theorem cell20_839887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 2].length) (baseStart_839887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839887 prefixEnd_839887 := by exact prefixLift 839887
  have htrace : WordTrace (prefixWord ++ tailWord_839887) baseStart_839887 baseEnd_839887 := by
    simpa [prefixWord, tailWord_839887, baseEnd_839887] using wordTrace_append hprefix tailTrace_839887
  have hstable : (prefixWord ++ tailWord_839887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839887).length < 2 ^ (prefixWord ++ tailWord_839887).sum := by decide
  have hdescent : baseEnd_839887 < baseStart_839887 := by decide
  rcases family_descends (prefixWord ++ tailWord_839887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839907 : List Nat := [1, 1, 1, 8, 2, 1, 2, 4]
def baseStart_839907 : Nat := 118140960795 + 839907 * 2 ^ 59
def prefixEnd_839907 : Nat := 4983230072969 + 3 ^ 40 * 839907 * 2
def baseEnd_839907 : Nat := 127785480318800175911065

theorem tailTrace_839907 : CollatzResearch.WordTrace tailWord_839907 prefixEnd_839907 127785480318800175911065 := by
  unfold tailWord_839907
  simp only [CollatzResearch.WordTrace]
  refine ⟨30633924968167858540493975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20422616645445239026995983 30633924968167858540493975)
  ·
    refine ⟨45950887452251787810740963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30633924968167858540493975 45950887452251787810740963)
    ·
      refine ⟨68926331178377681716111445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45950887452251787810740963 68926331178377681716111445)
      ·
        refine ⟨807730443496613457610681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 68926331178377681716111445 807730443496613457610681)
        ·
          refine ⟨605797832622460093208011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807730443496613457610681 605797832622460093208011)
          ·
            refine ⟨908696748933690139812017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605797832622460093208011 908696748933690139812017)
            ·
              refine ⟨681522561700267604859013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908696748933690139812017 681522561700267604859013)
              ·
                refine ⟨127785480318800175911065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681522561700267604859013 127785480318800175911065)
                ·
                  rfl

theorem cell20_839907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 4].length) (baseStart_839907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839907 prefixEnd_839907 := by exact prefixLift 839907
  have htrace : WordTrace (prefixWord ++ tailWord_839907) baseStart_839907 baseEnd_839907 := by
    simpa [prefixWord, tailWord_839907, baseEnd_839907] using wordTrace_append hprefix tailTrace_839907
  have hstable : (prefixWord ++ tailWord_839907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839907).length < 2 ^ (prefixWord ++ tailWord_839907).sum := by decide
  have hdescent : baseEnd_839907 < baseStart_839907 := by decide
  rcases family_descends (prefixWord ++ tailWord_839907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839911 : List Nat := [1, 1, 5, 3, 1, 1, 4, 4]
def baseStart_839911 : Nat := 118140960795 + 839911 * 2 ^ 59
def prefixEnd_839911 : Nat := 4983230072969 + 3 ^ 40 * 839911 * 2
def baseEnd_839911 : Nat := 127786088888464763866615

theorem tailTrace_839911 : CollatzResearch.WordTrace tailWord_839911 prefixEnd_839911 127786088888464763866615 := by
  unfold tailWord_839911
  simp only [CollatzResearch.WordTrace]
  refine ⟨30634070860153367223639587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20422713906768911482426391 30634070860153367223639587)
  ·
    refine ⟨45951106290230050835459381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30634070860153367223639587 45951106290230050835459381)
    ·
      refine ⟨4307916214709067265824317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45951106290230050835459381 4307916214709067265824317)
      ·
        refine ⟨1615468580515900224684119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4307916214709067265824317 1615468580515900224684119)
        ·
          refine ⟨2423202870773850337026179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615468580515900224684119 2423202870773850337026179)
          ·
            refine ⟨3634804306160775505539269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423202870773850337026179 3634804306160775505539269)
            ·
              refine ⟨681525807405145407288613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3634804306160775505539269 681525807405145407288613)
              ·
                refine ⟨127786088888464763866615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681525807405145407288613 127786088888464763866615)
                ·
                  rfl

theorem cell20_839911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 4].length) (baseStart_839911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839911 prefixEnd_839911 := by exact prefixLift 839911
  have htrace : WordTrace (prefixWord ++ tailWord_839911) baseStart_839911 baseEnd_839911 := by
    simpa [prefixWord, tailWord_839911, baseEnd_839911] using wordTrace_append hprefix tailTrace_839911
  have hstable : (prefixWord ++ tailWord_839911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839911).length < 2 ^ (prefixWord ++ tailWord_839911).sum := by decide
  have hdescent : baseEnd_839911 < baseStart_839911 := by decide
  rcases family_descends (prefixWord ++ tailWord_839911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839915 : List Nat := [1, 1, 1, 1, 2, 5, 3, 6]
def baseStart_839915 : Nat := 118140960795 + 839915 * 2 ^ 59
def prefixEnd_839915 : Nat := 4983230072969 + 3 ^ 40 * 839915 * 2
def baseEnd_839915 : Nat := 127786697458129351822165

theorem tailTrace_839915 : CollatzResearch.WordTrace tailWord_839915 prefixEnd_839915 127786697458129351822165 := by
  unfold tailWord_839915
  simp only [CollatzResearch.WordTrace]
  refine ⟨30634216752138875906785199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20422811168092583937856799 30634216752138875906785199)
  ·
    refine ⟨45951325128208313860177799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30634216752138875906785199 45951325128208313860177799)
    ·
      refine ⟨68926987692312470790266699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45951325128208313860177799 68926987692312470790266699)
      ·
        refine ⟨103390481538468706185400049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68926987692312470790266699 103390481538468706185400049)
        ·
          refine ⟨77542861153851529639050037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103390481538468706185400049 77542861153851529639050037)
          ·
            refine ⟨7269643233173580903660941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77542861153851529639050037 7269643233173580903660941)
            ·
              refine ⟨2726116212440092838872853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7269643233173580903660941 2726116212440092838872853)
              ·
                refine ⟨127786697458129351822165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2726116212440092838872853 127786697458129351822165)
                ·
                  rfl

theorem cell20_839915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_839915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839915 prefixEnd_839915 := by exact prefixLift 839915
  have htrace : WordTrace (prefixWord ++ tailWord_839915) baseStart_839915 baseEnd_839915 := by
    simpa [prefixWord, tailWord_839915, baseEnd_839915] using wordTrace_append hprefix tailTrace_839915
  have hstable : (prefixWord ++ tailWord_839915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839915).length < 2 ^ (prefixWord ++ tailWord_839915).sum := by decide
  have hdescent : baseEnd_839915 < baseStart_839915 := by decide
  rcases family_descends (prefixWord ++ tailWord_839915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839932 : List Nat := [2, 2, 2, 1, 4, 3, 6]
def baseStart_839932 : Nat := 118140960795 + 839932 * 2 ^ 59
def prefixEnd_839932 : Nat := 4983230072969 + 3 ^ 40 * 839932 * 2
def baseEnd_839932 : Nat := 42596427959734616877751

theorem tailTrace_839932 : CollatzResearch.WordTrace tailWord_839932 prefixEnd_839932 42596427959734616877751 := by
  unfold tailWord_839932
  simp only [CollatzResearch.WordTrace]
  refine ⟨15317418396538643905077025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20423224528718191873436033 15317418396538643905077025)
  ·
    refine ⟨11488063797403982928807769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15317418396538643905077025 11488063797403982928807769)
    ·
      refine ⟨8616047848052987196605827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11488063797403982928807769 8616047848052987196605827)
      ·
        refine ⟨12924071772079480794908741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8616047848052987196605827 12924071772079480794908741)
        ·
          refine ⟨2423263457264902649045389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12924071772079480794908741 2423263457264902649045389)
          ·
            refine ⟨908723796474338493392021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2423263457264902649045389 908723796474338493392021)
            ·
              refine ⟨42596427959734616877751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 908723796474338493392021 42596427959734616877751)
              ·
                rfl

theorem cell20_839932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 6].length) (baseStart_839932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839932 prefixEnd_839932 := by exact prefixLift 839932
  have htrace : WordTrace (prefixWord ++ tailWord_839932) baseStart_839932 baseEnd_839932 := by
    simpa [prefixWord, tailWord_839932, baseEnd_839932] using wordTrace_append hprefix tailTrace_839932
  have hstable : (prefixWord ++ tailWord_839932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839932).length < 2 ^ (prefixWord ++ tailWord_839932).sum := by decide
  have hdescent : baseEnd_839932 < baseStart_839932 := by decide
  rcases family_descends (prefixWord ++ tailWord_839932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839938 : List Nat := [3, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_839938 : Nat := 118140960795 + 839938 * 2 ^ 59
def prefixEnd_839938 : Nat := 4983230072969 + 3 ^ 40 * 839938 * 2
def baseEnd_839938 : Nat := 383370590201102197699735

theorem tailTrace_839938 : CollatzResearch.WordTrace tailWord_839938 prefixEnd_839938 383370590201102197699735 := by
  unfold tailWord_839938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658763907763887708718117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20423370420703700556581645 7658763907763887708718117)
  ·
    refine ⟨1436018232705728945384647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7658763907763887708718117 1436018232705728945384647)
    ·
      refine ⟨2154027349058593418076971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436018232705728945384647 2154027349058593418076971)
      ·
        refine ⟨3231041023587890127115457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154027349058593418076971 3231041023587890127115457)
        ·
          refine ⟨2423280767690917595336593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3231041023587890127115457 2423280767690917595336593)
          ·
            refine ⟨1817460575768188196502445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423280767690917595336593 1817460575768188196502445)
            ·
              refine ⟨681547715913070573688417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1817460575768188196502445 681547715913070573688417)
              ·
                refine ⟨511160786934802930266313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681547715913070573688417 511160786934802930266313)
                ·
                  refine ⟨383370590201102197699735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511160786934802930266313 383370590201102197699735)
                  ·
                    rfl

theorem cell20_839938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_839938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839938 prefixEnd_839938 := by exact prefixLift 839938
  have htrace : WordTrace (prefixWord ++ tailWord_839938) baseStart_839938 baseEnd_839938 := by
    simpa [prefixWord, tailWord_839938, baseEnd_839938] using wordTrace_append hprefix tailTrace_839938
  have hstable : (prefixWord ++ tailWord_839938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839938).length < 2 ^ (prefixWord ++ tailWord_839938).sum := by decide
  have hdescent : baseEnd_839938 < baseStart_839938 := by decide
  rcases family_descends (prefixWord ++ tailWord_839938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839939 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 3]
def baseStart_839939 : Nat := 118140960795 + 839939 * 2 ^ 59
def prefixEnd_839939 : Nat := 4983230072969 + 3 ^ 40 * 839939 * 2
def baseEnd_839939 : Nat := 383371046628350638666397

theorem tailTrace_839939 : CollatzResearch.WordTrace tailWord_839939 prefixEnd_839939 383371046628350638666397 := by
  unfold tailWord_839939
  simp only [CollatzResearch.WordTrace]
  refine ⟨30635092104051928005658871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20423394736034618670439247 30635092104051928005658871)
  ·
    refine ⟨45952638156077892008488307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30635092104051928005658871 45952638156077892008488307)
    ·
      refine ⟨68928957234116838012732461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45952638156077892008488307 68928957234116838012732461)
      ·
        refine ⟨25848358962793814254774673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68928957234116838012732461 25848358962793814254774673)
        ·
          refine ⟨19386269222095360691081005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25848358962793814254774673 19386269222095360691081005)
          ·
            refine ⟨7269850958285760259155377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19386269222095360691081005 7269850958285760259155377)
            ·
              refine ⟨5452388218714320194366533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7269850958285760259155377 5452388218714320194366533)
              ·
                refine ⟨1022322791008935036443725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5452388218714320194366533 1022322791008935036443725)
                ·
                  refine ⟨383371046628350638666397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022322791008935036443725 383371046628350638666397)
                  ·
                    rfl

theorem cell20_839939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_839939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839939 prefixEnd_839939 := by exact prefixLift 839939
  have htrace : WordTrace (prefixWord ++ tailWord_839939) baseStart_839939 baseEnd_839939 := by
    simpa [prefixWord, tailWord_839939, baseEnd_839939] using wordTrace_append hprefix tailTrace_839939
  have hstable : (prefixWord ++ tailWord_839939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839939).length < 2 ^ (prefixWord ++ tailWord_839939).sum := by decide
  have hdescent : baseEnd_839939 < baseStart_839939 := by decide
  rcases family_descends (prefixWord ++ tailWord_839939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839953 : List Nat := [1, 2, 2, 1, 1, 5, 1, 7]
def baseStart_839953 : Nat := 118140960795 + 839953 * 2 ^ 59
def prefixEnd_839953 : Nat := 4983230072969 + 3 ^ 40 * 839953 * 2
def baseEnd_839953 : Nat := 127792478869942937399891

theorem tailTrace_839953 : CollatzResearch.WordTrace tailWord_839953 prefixEnd_839953 127792478869942937399891 := by
  unfold tailWord_839953
  simp only [CollatzResearch.WordTrace]
  refine ⟨30635602726001208396668513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20423735150667472264445675 30635602726001208396668513)
  ·
    refine ⟨22976702044500906297501385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30635602726001208396668513 22976702044500906297501385)
    ·
      refine ⟨17232526533375679723126039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22976702044500906297501385 17232526533375679723126039)
      ·
        refine ⟨25848789800063519584689059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17232526533375679723126039 25848789800063519584689059)
        ·
          refine ⟨38773184700095279377033589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25848789800063519584689059 38773184700095279377033589)
          ·
            refine ⟨3634986065633932441596899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38773184700095279377033589 3634986065633932441596899)
            ·
              refine ⟨5452479098450898662395349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634986065633932441596899 5452479098450898662395349)
              ·
                refine ⟨127792478869942937399891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5452479098450898662395349 127792478869942937399891)
                ·
                  rfl

theorem cell20_839953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_839953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839953 prefixEnd_839953 := by exact prefixLift 839953
  have htrace : WordTrace (prefixWord ++ tailWord_839953) baseStart_839953 baseEnd_839953 := by
    simpa [prefixWord, tailWord_839953, baseEnd_839953] using wordTrace_append hprefix tailTrace_839953
  have hstable : (prefixWord ++ tailWord_839953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839953).length < 2 ^ (prefixWord ++ tailWord_839953).sum := by decide
  have hdescent : baseEnd_839953 < baseStart_839953 := by decide
  rcases family_descends (prefixWord ++ tailWord_839953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839970 : List Nat := [3, 3, 1, 1, 3, 1, 2, 6]
def baseStart_839970 : Nat := 118140960795 + 839970 * 2 ^ 59
def prefixEnd_839970 : Nat := 4983230072969 + 3 ^ 40 * 839970 * 2
def baseEnd_839970 : Nat := 127795065291017436210979

theorem tailTrace_839970 : CollatzResearch.WordTrace tailWord_839970 prefixEnd_839970 127795065291017436210979 := by
  unfold tailWord_839970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659055691734905075009341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20424148511293080200024909 7659055691734905075009341)
  ·
    refine ⟨2872145884400589403128503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7659055691734905075009341 2872145884400589403128503)
    ·
      refine ⟨4308218826600884104692755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872145884400589403128503 4308218826600884104692755)
      ·
        refine ⟨6462328239901326157039133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308218826600884104692755 6462328239901326157039133)
        ·
          refine ⟨2423373089962997308889675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6462328239901326157039133 2423373089962997308889675)
          ·
            refine ⟨3635059634944495963334513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423373089962997308889675 3635059634944495963334513)
            ·
              refine ⟨2726294726208371972500885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3635059634944495963334513 2726294726208371972500885)
              ·
                refine ⟨127795065291017436210979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2726294726208371972500885 127795065291017436210979)
                ·
                  rfl

theorem cell20_839970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_839970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839970 prefixEnd_839970 := by exact prefixLift 839970
  have htrace : WordTrace (prefixWord ++ tailWord_839970) baseStart_839970 baseEnd_839970 := by
    simpa [prefixWord, tailWord_839970, baseEnd_839970] using wordTrace_append hprefix tailTrace_839970
  have hstable : (prefixWord ++ tailWord_839970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839970).length < 2 ^ (prefixWord ++ tailWord_839970).sum := by decide
  have hdescent : baseEnd_839970 < baseStart_839970 := by decide
  rcases family_descends (prefixWord ++ tailWord_839970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839994 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_839994 : Nat := 118140960795 + 839994 * 2 ^ 59
def prefixEnd_839994 : Nat := 4983230072969 + 3 ^ 40 * 839994 * 2
def baseEnd_839994 : Nat := 383396150127014891832839

theorem tailTrace_839994 : CollatzResearch.WordTrace tailWord_839994 prefixEnd_839994 383396150127014891832839 := by
  unfold tailWord_839994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659274529713168099727759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20424732079235114932607357 7659274529713168099727759)
  ·
    refine ⟨11488911794569752149591639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7659274529713168099727759 11488911794569752149591639)
    ·
      refine ⟨17233367691854628224387459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11488911794569752149591639 17233367691854628224387459)
      ·
        refine ⟨25850051537781942336581189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17233367691854628224387459 25850051537781942336581189)
        ·
          refine ⟨4846884663334114188108973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25850051537781942336581189 4846884663334114188108973)
          ·
            refine ⟨1817581748750292820540865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4846884663334114188108973 1817581748750292820540865)
            ·
              refine ⟨1363186311562719615405649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817581748750292820540865 1363186311562719615405649)
              ·
                refine ⟨1022389733672039711554237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363186311562719615405649 1022389733672039711554237)
                ·
                  refine ⟨383396150127014891832839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022389733672039711554237 383396150127014891832839)
                  ·
                    rfl

theorem cell20_839994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_839994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_839994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_839994 prefixEnd_839994 := by exact prefixLift 839994
  have htrace : WordTrace (prefixWord ++ tailWord_839994) baseStart_839994 baseEnd_839994 := by
    simpa [prefixWord, tailWord_839994, baseEnd_839994] using wordTrace_append hprefix tailTrace_839994
  have hstable : (prefixWord ++ tailWord_839994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839994).length < 2 ^ (prefixWord ++ tailWord_839994).sum := by decide
  have hdescent : baseEnd_839994 < baseStart_839994 := by decide
  rcases family_descends (prefixWord ++ tailWord_839994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840004 : List Nat := [2, 3, 4, 1, 2, 2, 1, 5]
def baseStart_840004 : Nat := 118140960795 + 840004 * 2 ^ 59
def prefixEnd_840004 : Nat := 4983230072969 + 3 ^ 40 * 840004 * 2
def baseEnd_840004 : Nat := 127800238133166433833155

theorem tailTrace_840004 : CollatzResearch.WordTrace tailWord_840004 prefixEnd_840004 127800238133166433833155 := by
  unfold tailWord_840004
  simp only [CollatzResearch.WordTrace]
  refine ⟨15318731424408222053387533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20424975232544296071183377 15318731424408222053387533)
  ·
    refine ⟨5744524284153083270020325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15318731424408222053387533 5744524284153083270020325)
    ·
      refine ⟨1077098303278703113128811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5744524284153083270020325 1077098303278703113128811)
      ·
        refine ⟨1615647454918054669693217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077098303278703113128811 1615647454918054669693217)
        ·
          refine ⟨1211735591188541002269913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615647454918054669693217 1211735591188541002269913)
          ·
            refine ⟨908801693391405751702435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1211735591188541002269913 908801693391405751702435)
            ·
              refine ⟨1363202540087108627553653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908801693391405751702435 1363202540087108627553653)
              ·
                refine ⟨127800238133166433833155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1363202540087108627553653 127800238133166433833155)
                ·
                  rfl

theorem cell20_840004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_840004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840004 prefixEnd_840004 := by exact prefixLift 840004
  have htrace : WordTrace (prefixWord ++ tailWord_840004) baseStart_840004 baseEnd_840004 := by
    simpa [prefixWord, tailWord_840004, baseEnd_840004] using wordTrace_append hprefix tailTrace_840004
  have hstable : (prefixWord ++ tailWord_840004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840004).length < 2 ^ (prefixWord ++ tailWord_840004).sum := by decide
  have hdescent : baseEnd_840004 < baseStart_840004 := by decide
  rcases family_descends (prefixWord ++ tailWord_840004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840086 : List Nat := [5, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_840086 : Nat := 118140960795 + 840086 * 2 ^ 59
def prefixEnd_840086 : Nat := 4983230072969 + 3 ^ 40 * 840086 * 2
def baseEnd_840086 : Nat := 383438141433871460765797

theorem tailTrace_840086 : CollatzResearch.WordTrace tailWord_840086 prefixEnd_840086 383438141433871460765797 := by
  unfold tailWord_840086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915028352157460756953757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20426969089679581407506741 1915028352157460756953757)
  ·
    refine ⟨718135632059047783857659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1915028352157460756953757 718135632059047783857659)
    ·
      refine ⟨1077203448088571675786489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 718135632059047783857659 1077203448088571675786489)
      ·
        refine ⟨807902586066428756839867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1077203448088571675786489 807902586066428756839867)
        ·
          refine ⟨1211853879099643135259801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807902586066428756839867 1211853879099643135259801)
          ·
            refine ⟨908890409324732351444851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1211853879099643135259801 908890409324732351444851)
            ·
              refine ⟨1363335613987098527167277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908890409324732351444851 1363335613987098527167277)
              ·
                refine ⟨511250855245161947687729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1363335613987098527167277 511250855245161947687729)
                ·
                  refine ⟨383438141433871460765797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511250855245161947687729 383438141433871460765797)
                  ·
                    rfl

theorem cell20_840086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_840086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840086 prefixEnd_840086 := by exact prefixLift 840086
  have htrace : WordTrace (prefixWord ++ tailWord_840086) baseStart_840086 baseEnd_840086 := by
    simpa [prefixWord, tailWord_840086, baseEnd_840086] using wordTrace_append hprefix tailTrace_840086
  have hstable : (prefixWord ++ tailWord_840086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840086).length < 2 ^ (prefixWord ++ tailWord_840086).sum := by decide
  have hdescent : baseEnd_840086 < baseStart_840086 := by decide
  rcases family_descends (prefixWord ++ tailWord_840086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840125 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 3]
def baseStart_840125 : Nat := 118140960795 + 840125 * 2 ^ 59
def prefixEnd_840125 : Nat := 4983230072969 + 3 ^ 40 * 840125 * 2
def baseEnd_840125 : Nat := 383455942096560658465637

theorem tailTrace_840125 : CollatzResearch.WordTrace tailWord_840125 prefixEnd_840125 383455942096560658465637 := by
  unfold tailWord_840125
  simp only [CollatzResearch.WordTrace]
  refine ⟨30641876081378081771929829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20427917387585387847953219 30641876081378081771929829)
  ·
    refine ⟨5745351765258390332236843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30641876081378081771929829 5745351765258390332236843)
    ·
      refine ⟨8618027647887585498355265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5745351765258390332236843 8618027647887585498355265)
      ·
        refine ⟨6463520735915689123766449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8618027647887585498355265 6463520735915689123766449)
        ·
          refine ⟨4847640551936766842824837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6463520735915689123766449 4847640551936766842824837)
          ·
            refine ⟨908932603488143783029657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4847640551936766842824837 908932603488143783029657)
            ·
              refine ⟨681699452616107837272243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908932603488143783029657 681699452616107837272243)
              ·
                refine ⟨1022549178924161755908365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681699452616107837272243 1022549178924161755908365)
                ·
                  refine ⟨383455942096560658465637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022549178924161755908365 383455942096560658465637)
                  ·
                    rfl

theorem cell20_840125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_840125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840125 prefixEnd_840125 := by exact prefixLift 840125
  have htrace : WordTrace (prefixWord ++ tailWord_840125) baseStart_840125 baseEnd_840125 := by
    simpa [prefixWord, tailWord_840125, baseEnd_840125] using wordTrace_append hprefix tailTrace_840125
  have hstable : (prefixWord ++ tailWord_840125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840125).length < 2 ^ (prefixWord ++ tailWord_840125).sum := by decide
  have hdescent : baseEnd_840125 < baseStart_840125 := by decide
  rcases family_descends (prefixWord ++ tailWord_840125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840153 : List Nat := [1, 2, 1, 2, 4, 1, 2, 5, 2]
def baseStart_840153 : Nat := 118140960795 + 840153 * 2 ^ 59
def prefixEnd_840153 : Nat := 4983230072969 + 3 ^ 40 * 840153 * 2
def baseEnd_840153 : Nat := 383468722059517005532189

theorem tailTrace_840153 : CollatzResearch.WordTrace tailWord_840153 prefixEnd_840153 383468722059517005532189 := by
  unfold tailWord_840153
  simp only [CollatzResearch.WordTrace]
  refine ⟨30642897325276642553949113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20428598216851095035966075 30642897325276642553949113)
  ·
    refine ⟨22982172993957481915461835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30642897325276642553949113 22982172993957481915461835)
    ·
      refine ⟨34473259490936222873192753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22982172993957481915461835 34473259490936222873192753)
      ·
        refine ⟨25854944618202167154894565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34473259490936222873192753 25854944618202167154894565)
        ·
          refine ⟨4847802115912906341542731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25854944618202167154894565 4847802115912906341542731)
          ·
            refine ⟨7271703173869359512314097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847802115912906341542731 7271703173869359512314097)
            ·
              refine ⟨5453777380402019634235573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7271703173869359512314097 5453777380402019634235573)
              ·
                refine ⟨511291629412689340709585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5453777380402019634235573 511291629412689340709585)
                ·
                  refine ⟨383468722059517005532189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511291629412689340709585 383468722059517005532189)
                  ·
                    rfl

theorem cell20_840153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_840153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840153 prefixEnd_840153 := by exact prefixLift 840153
  have htrace : WordTrace (prefixWord ++ tailWord_840153) baseStart_840153 baseEnd_840153 := by
    simpa [prefixWord, tailWord_840153, baseEnd_840153] using wordTrace_append hprefix tailTrace_840153
  have hstable : (prefixWord ++ tailWord_840153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840153).length < 2 ^ (prefixWord ++ tailWord_840153).sum := by decide
  have hdescent : baseEnd_840153 < baseStart_840153 := by decide
  rcases family_descends (prefixWord ++ tailWord_840153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840162 : List Nat := [3, 3, 3, 2, 2, 1, 2, 2, 2]
def baseStart_840162 : Nat := 118140960795 + 840162 * 2 ^ 59
def prefixEnd_840162 : Nat := 4983230072969 + 3 ^ 40 * 840162 * 2
def baseEnd_840162 : Nat := 383472829904752974232153

theorem tailTrace_840162 : CollatzResearch.WordTrace tailWord_840162 prefixEnd_840162 383472829904752974232153 := by
  unfold tailWord_840162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7660806395561009272756685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20428817054829358060684493 7660806395561009272756685)
  ·
    refine ⟨2872802398335378477283757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7660806395561009272756685 2872802398335378477283757)
    ·
      refine ⟨1077300899375766928981409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2872802398335378477283757 1077300899375766928981409)
      ·
        refine ⟨807975674531825196736057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1077300899375766928981409 807975674531825196736057)
        ·
          refine ⟨605981755898868897552043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807975674531825196736057 605981755898868897552043)
          ·
            refine ⟨908972633848303346328065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605981755898868897552043 908972633848303346328065)
            ·
              refine ⟨681729475386227509746049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908972633848303346328065 681729475386227509746049)
              ·
                refine ⟨511297106539670632309537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681729475386227509746049 511297106539670632309537)
                ·
                  refine ⟨383472829904752974232153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511297106539670632309537 383472829904752974232153)
                  ·
                    rfl

theorem cell20_840162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_840162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840162 prefixEnd_840162 := by exact prefixLift 840162
  have htrace : WordTrace (prefixWord ++ tailWord_840162) baseStart_840162 baseEnd_840162 := by
    simpa [prefixWord, tailWord_840162, baseEnd_840162] using wordTrace_append hprefix tailTrace_840162
  have hstable : (prefixWord ++ tailWord_840162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840162).length < 2 ^ (prefixWord ++ tailWord_840162).sum := by decide
  have hdescent : baseEnd_840162 < baseStart_840162 := by decide
  rcases family_descends (prefixWord ++ tailWord_840162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840170 : List Nat := [3, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_840170 : Nat := 118140960795 + 840170 * 2 ^ 59
def prefixEnd_840170 : Nat := 4983230072969 + 3 ^ 40 * 840170 * 2
def baseEnd_840170 : Nat := 383476481322740501965453

theorem tailTrace_840170 : CollatzResearch.WordTrace tailWord_840170 prefixEnd_840170 383476481322740501965453 := by
  unfold tailWord_840170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7660879341553763614329491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20429011577476702971545309 7660879341553763614329491)
  ·
    refine ⟨11491319012330645421494237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7660879341553763614329491 11491319012330645421494237)
    ·
      refine ⟨4309244629623992033060339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11491319012330645421494237 4309244629623992033060339)
      ·
        refine ⟨6463866944435988049590509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4309244629623992033060339 6463866944435988049590509)
        ·
          refine ⟨2423950104163495518596441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6463866944435988049590509 2423950104163495518596441)
          ·
            refine ⟨1817962578122621638947331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423950104163495518596441 1817962578122621638947331)
            ·
              refine ⟨2726943867183932458420997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817962578122621638947331 2726943867183932458420997)
              ·
                refine ⟨511301975096987335953937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2726943867183932458420997 511301975096987335953937)
                ·
                  refine ⟨383476481322740501965453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511301975096987335953937 383476481322740501965453)
                  ·
                    rfl

theorem cell20_840170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_840170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840170 prefixEnd_840170 := by exact prefixLift 840170
  have htrace : WordTrace (prefixWord ++ tailWord_840170) baseStart_840170 baseEnd_840170 := by
    simpa [prefixWord, tailWord_840170, baseEnd_840170] using wordTrace_append hprefix tailTrace_840170
  have hstable : (prefixWord ++ tailWord_840170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840170).length < 2 ^ (prefixWord ++ tailWord_840170).sum := by decide
  have hdescent : baseEnd_840170 < baseStart_840170 := by decide
  rcases family_descends (prefixWord ++ tailWord_840170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840188 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_840188 : Nat := 118140960795 + 840188 * 2 ^ 59
def prefixEnd_840188 : Nat := 4983230072969 + 3 ^ 40 * 840188 * 2
def baseEnd_840188 : Nat := 383484697013212439365379

theorem tailTrace_840188 : CollatzResearch.WordTrace tailWord_840188 prefixEnd_840188 383484697013212439365379 := by
  unfold tailWord_840188
  simp only [CollatzResearch.WordTrace]
  refine ⟨15322086940074921765736609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20429449253433229020982145 15322086940074921765736609)
  ·
    refine ⟨11491565205056191324302457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15322086940074921765736609 11491565205056191324302457)
    ·
      refine ⟨8618673903792143493226843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11491565205056191324302457 8618673903792143493226843)
      ·
        refine ⟨12928010855688215239840265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8618673903792143493226843 12928010855688215239840265)
        ·
          refine ⟨9696008141766161429880199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12928010855688215239840265 9696008141766161429880199)
          ·
            refine ⟨14544012212649242144820299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9696008141766161429880199 14544012212649242144820299)
            ·
              refine ⟨21816018318973863217230449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14544012212649242144820299 21816018318973863217230449)
              ·
                refine ⟨16362013739230397412922837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21816018318973863217230449 16362013739230397412922837)
                ·
                  refine ⟨383484697013212439365379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16362013739230397412922837 383484697013212439365379)
                  ·
                    rfl

theorem cell20_840188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_840188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840188 prefixEnd_840188 := by exact prefixLift 840188
  have htrace : WordTrace (prefixWord ++ tailWord_840188) baseStart_840188 baseEnd_840188 := by
    simpa [prefixWord, tailWord_840188, baseEnd_840188] using wordTrace_append hprefix tailTrace_840188
  have hstable : (prefixWord ++ tailWord_840188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840188).length < 2 ^ (prefixWord ++ tailWord_840188).sum := by decide
  have hdescent : baseEnd_840188 < baseStart_840188 := by decide
  rcases family_descends (prefixWord ++ tailWord_840188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840194 : List Nat := [3, 4, 1, 2, 2, 1, 3, 4]
def baseStart_840194 : Nat := 118140960795 + 840194 * 2 ^ 59
def prefixEnd_840194 : Nat := 4983230072969 + 3 ^ 40 * 840194 * 2
def baseEnd_840194 : Nat := 127829145192234361721785

theorem tailTrace_840194 : CollatzResearch.WordTrace tailWord_840194 prefixEnd_840194 127829145192234361721785 := by
  unfold tailWord_840194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7661098179532026639047909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20429595145418737704127757 7661098179532026639047909)
  ·
    refine ⟨1436455908662254994821483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7661098179532026639047909 1436455908662254994821483)
    ·
      refine ⟨2154683862993382492232225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436455908662254994821483 2154683862993382492232225)
      ·
        refine ⟨1616012897245036869174169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2154683862993382492232225 1616012897245036869174169)
        ·
          refine ⟨1212009672933777651880627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1616012897245036869174169 1212009672933777651880627)
          ·
            refine ⟨1818014509400666477820941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212009672933777651880627 1818014509400666477820941)
            ·
              refine ⟨681755441025249929182853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1818014509400666477820941 681755441025249929182853)
              ·
                refine ⟨127829145192234361721785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681755441025249929182853 127829145192234361721785)
                ·
                  rfl

theorem cell20_840194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_840194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840194 prefixEnd_840194 := by exact prefixLift 840194
  have htrace : WordTrace (prefixWord ++ tailWord_840194) baseStart_840194 baseEnd_840194 := by
    simpa [prefixWord, tailWord_840194, baseEnd_840194] using wordTrace_append hprefix tailTrace_840194
  have hstable : (prefixWord ++ tailWord_840194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840194).length < 2 ^ (prefixWord ++ tailWord_840194).sum := by decide
  have hdescent : baseEnd_840194 < baseStart_840194 := by decide
  rcases family_descends (prefixWord ++ tailWord_840194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840229 : List Nat := [1, 3, 1, 2, 2, 1, 4, 4, 2]
def baseStart_840229 : Nat := 118140960795 + 840229 * 2 ^ 59
def prefixEnd_840229 : Nat := 4983230072969 + 3 ^ 40 * 840229 * 2
def baseEnd_840229 : Nat := 383503410530398518998545

theorem tailTrace_840229 : CollatzResearch.WordTrace tailWord_840229 prefixEnd_840229 383503410530398518998545 := by
  unfold tailWord_840229
  simp only [CollatzResearch.WordTrace]
  refine ⟨30645669273001307533715741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20430446182000871689143827 30645669273001307533715741)
  ·
    refine ⟨11492125977375490325143403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30645669273001307533715741 11492125977375490325143403)
    ·
      refine ⟨17238188966063235487715105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11492125977375490325143403 17238188966063235487715105)
      ·
        refine ⟨12928641724547426615786329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17238188966063235487715105 12928641724547426615786329)
        ·
          refine ⟨9696481293410569961839747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12928641724547426615786329 9696481293410569961839747)
          ·
            refine ⟨14544721940115854942759621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9696481293410569961839747 14544721940115854942759621)
            ·
              refine ⟨2727135363771722801767429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14544721940115854942759621 2727135363771722801767429)
              ·
                refine ⟨511337880707198025331393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2727135363771722801767429 511337880707198025331393)
                ·
                  refine ⟨383503410530398518998545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511337880707198025331393 383503410530398518998545)
                  ·
                    rfl

theorem cell20_840229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_840229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840229 prefixEnd_840229 := by exact prefixLift 840229
  have htrace : WordTrace (prefixWord ++ tailWord_840229) baseStart_840229 baseEnd_840229 := by
    simpa [prefixWord, tailWord_840229, baseEnd_840229] using wordTrace_append hprefix tailTrace_840229
  have hstable : (prefixWord ++ tailWord_840229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840229).length < 2 ^ (prefixWord ++ tailWord_840229).sum := by decide
  have hdescent : baseEnd_840229 < baseStart_840229 := by decide
  rcases family_descends (prefixWord ++ tailWord_840229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840250 : List Nat := [3, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_840250 : Nat := 118140960795 + 840250 * 2 ^ 59
def prefixEnd_840250 : Nat := 4983230072969 + 3 ^ 40 * 840250 * 2
def baseEnd_840250 : Nat := 383512995502615779298459

theorem tailTrace_840250 : CollatzResearch.WordTrace tailWord_840250 prefixEnd_840250 383512995502615779298459 := by
  unfold tailWord_840250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7661608801481307030057551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20430956803950152080153469 7661608801481307030057551)
  ·
    refine ⟨11492413202221960545086327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7661608801481307030057551 11492413202221960545086327)
    ·
      refine ⟨17238619803332940817629491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11492413202221960545086327 17238619803332940817629491)
      ·
        refine ⟨25857929704999411226444237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17238619803332940817629491 25857929704999411226444237)
        ·
          refine ⟨9696723639374779209916589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25857929704999411226444237 9696723639374779209916589)
          ·
            refine ⟨3636271364765542203718721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9696723639374779209916589 3636271364765542203718721)
            ·
              refine ⟨2727203523574156652789041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3636271364765542203718721 2727203523574156652789041)
              ·
                refine ⟨2045402642680617489591781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2727203523574156652789041 2045402642680617489591781)
                ·
                  refine ⟨383512995502615779298459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045402642680617489591781 383512995502615779298459)
                  ·
                    rfl

theorem cell20_840250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_840250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840250 prefixEnd_840250 := by exact prefixLift 840250
  have htrace : WordTrace (prefixWord ++ tailWord_840250) baseStart_840250 baseEnd_840250 := by
    simpa [prefixWord, tailWord_840250, baseEnd_840250] using wordTrace_append hprefix tailTrace_840250
  have hstable : (prefixWord ++ tailWord_840250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840250).length < 2 ^ (prefixWord ++ tailWord_840250).sum := by decide
  have hdescent : baseEnd_840250 < baseStart_840250 := by decide
  rcases family_descends (prefixWord ++ tailWord_840250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840253 : List Nat := [1, 4, 1, 3, 2, 3, 2, 4]
def baseStart_840253 : Nat := 118140960795 + 840253 * 2 ^ 59
def prefixEnd_840253 : Nat := 4983230072969 + 3 ^ 40 * 840253 * 2
def baseEnd_840253 : Nat := 127838121594787034066149

theorem tailTrace_840253 : CollatzResearch.WordTrace tailWord_840253 prefixEnd_840253 127838121594787034066149 := by
  unfold tailWord_840253
  simp only [CollatzResearch.WordTrace]
  refine ⟨30646544624914359632589413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20431029749942906421726275 30646544624914359632589413)
  ·
    refine ⟨5746227117171442431110515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30646544624914359632589413 5746227117171442431110515)
    ·
      refine ⟨8619340675757163646665773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746227117171442431110515 8619340675757163646665773)
      ·
        refine ⟨3232252753408936367499665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8619340675757163646665773 3232252753408936367499665)
        ·
          refine ⟨2424189565056702275624749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3232252753408936367499665 2424189565056702275624749)
          ·
            refine ⟨909071086896263353359281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2424189565056702275624749 909071086896263353359281)
            ·
              refine ⟨681803315172197515019461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909071086896263353359281 681803315172197515019461)
              ·
                refine ⟨127838121594787034066149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 681803315172197515019461 127838121594787034066149)
                ·
                  rfl

theorem cell20_840253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 4].length) (baseStart_840253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840253 prefixEnd_840253 := by exact prefixLift 840253
  have htrace : WordTrace (prefixWord ++ tailWord_840253) baseStart_840253 baseEnd_840253 := by
    simpa [prefixWord, tailWord_840253, baseEnd_840253] using wordTrace_append hprefix tailTrace_840253
  have hstable : (prefixWord ++ tailWord_840253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840253).length < 2 ^ (prefixWord ++ tailWord_840253).sum := by decide
  have hdescent : baseEnd_840253 < baseStart_840253 := by decide
  rcases family_descends (prefixWord ++ tailWord_840253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840267 : List Nat := [1, 1, 1, 1, 3, 1, 7, 3, 2]
def baseStart_840267 : Nat := 118140960795 + 840267 * 2 ^ 59
def prefixEnd_840267 : Nat := 4983230072969 + 3 ^ 40 * 840267 * 2
def baseEnd_840267 : Nat := 383520754765839275731723

theorem tailTrace_840267 : CollatzResearch.WordTrace tailWord_840267 prefixEnd_840267 383520754765839275731723 := by
  unfold tailWord_840267
  simp only [CollatzResearch.WordTrace]
  refine ⟨30647055246863640023599055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20431370164575760015732703 30647055246863640023599055)
  ·
    refine ⟨45970582870295460035398583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30647055246863640023599055 45970582870295460035398583)
    ·
      refine ⟨68955874305443190053097875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45970582870295460035398583 68955874305443190053097875)
      ·
        refine ⟨103433811458164785079646813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68955874305443190053097875 103433811458164785079646813)
        ·
          refine ⟨38787679296811794404867555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103433811458164785079646813 38787679296811794404867555)
          ·
            refine ⟨58181518945217691607301333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38787679296811794404867555 58181518945217691607301333)
            ·
              refine ⟨1363629350278539647046125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58181518945217691607301333 1363629350278539647046125)
              ·
                refine ⟨511361006354452367642297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1363629350278539647046125 511361006354452367642297)
                ·
                  refine ⟨383520754765839275731723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511361006354452367642297 383520754765839275731723)
                  ·
                    rfl

theorem cell20_840267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 2].length) (baseStart_840267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840267 prefixEnd_840267 := by exact prefixLift 840267
  have htrace : WordTrace (prefixWord ++ tailWord_840267) baseStart_840267 baseEnd_840267 := by
    simpa [prefixWord, tailWord_840267, baseEnd_840267] using wordTrace_append hprefix tailTrace_840267
  have hstable : (prefixWord ++ tailWord_840267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840267).length < 2 ^ (prefixWord ++ tailWord_840267).sum := by decide
  have hdescent : baseEnd_840267 < baseStart_840267 := by decide
  rcases family_descends (prefixWord ++ tailWord_840267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840271 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_840271 : Nat := 118140960795 + 840271 * 2 ^ 59
def prefixEnd_840271 : Nat := 4983230072969 + 3 ^ 40 * 840271 * 2
def baseEnd_840271 : Nat := 383522580474833039598373

theorem tailTrace_840271 : CollatzResearch.WordTrace tailWord_840271 prefixEnd_840271 383522580474833039598373 := by
  unfold tailWord_840271
  simp only [CollatzResearch.WordTrace]
  refine ⟨30647201138849148706744667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20431467425899432471163111 30647201138849148706744667)
  ·
    refine ⟨45970801708273723060117001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30647201138849148706744667 45970801708273723060117001)
    ·
      refine ⟨34478101281205292295087751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45970801708273723060117001 34478101281205292295087751)
      ·
        refine ⟨51717151921807938442631627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34478101281205292295087751 51717151921807938442631627)
        ·
          refine ⟨77575727882711907663947441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51717151921807938442631627 77575727882711907663947441)
          ·
            refine ⟨58181795912033930747960581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77575727882711907663947441 58181795912033930747960581)
            ·
              refine ⟨10909086733506362015242609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58181795912033930747960581 10909086733506362015242609)
              ·
                refine ⟨8181815050129771511431957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10909086733506362015242609 8181815050129771511431957)
                ·
                  refine ⟨383522580474833039598373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8181815050129771511431957 383522580474833039598373)
                  ·
                    rfl

theorem cell20_840271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_840271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840271 prefixEnd_840271 := by exact prefixLift 840271
  have htrace : WordTrace (prefixWord ++ tailWord_840271) baseStart_840271 baseEnd_840271 := by
    simpa [prefixWord, tailWord_840271, baseEnd_840271] using wordTrace_append hprefix tailTrace_840271
  have hstable : (prefixWord ++ tailWord_840271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840271).length < 2 ^ (prefixWord ++ tailWord_840271).sum := by decide
  have hdescent : baseEnd_840271 < baseStart_840271 := by decide
  rcases family_descends (prefixWord ++ tailWord_840271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840284 : List Nat := [2, 2, 4, 1, 3, 2, 1, 1, 4]
def baseStart_840284 : Nat := 118140960795 + 840284 * 2 ^ 59
def prefixEnd_840284 : Nat := 4983230072969 + 3 ^ 40 * 840284 * 2
def baseEnd_840284 : Nat := 383528514029062772164987

theorem tailTrace_840284 : CollatzResearch.WordTrace tailWord_840284 prefixEnd_840284 383528514029062772164987 := by
  unfold tailWord_840284
  simp only [CollatzResearch.WordTrace]
  refine ⟨15323837643901025963483953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20431783525201367951311937 15323837643901025963483953)
  ·
    refine ⟨11492878232925769472612965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15323837643901025963483953 11492878232925769472612965)
    ·
      refine ⟨2154914668673581776114931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11492878232925769472612965 2154914668673581776114931)
      ·
        refine ⟨3232372003010372664172397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154914668673581776114931 3232372003010372664172397)
        ·
          refine ⟨1212139501128889749064649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3232372003010372664172397 1212139501128889749064649)
          ·
            refine ⟨909104625846667311798487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212139501128889749064649 909104625846667311798487)
            ·
              refine ⟨1363656938770000967697731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909104625846667311798487 1363656938770000967697731)
              ·
                refine ⟨2045485408155001451546597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363656938770000967697731 2045485408155001451546597)
                ·
                  refine ⟨383528514029062772164987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045485408155001451546597 383528514029062772164987)
                  ·
                    rfl

theorem cell20_840284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_840284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840284 prefixEnd_840284 := by exact prefixLift 840284
  have htrace : WordTrace (prefixWord ++ tailWord_840284) baseStart_840284 baseEnd_840284 := by
    simpa [prefixWord, tailWord_840284, baseEnd_840284] using wordTrace_append hprefix tailTrace_840284
  have hstable : (prefixWord ++ tailWord_840284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840284).length < 2 ^ (prefixWord ++ tailWord_840284).sum := by decide
  have hdescent : baseEnd_840284 < baseStart_840284 := by decide
  rcases family_descends (prefixWord ++ tailWord_840284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840288 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_840288 : Nat := 118140960795 + 840288 * 2 ^ 59
def prefixEnd_840288 : Nat := 4983230072969 + 3 ^ 40 * 840288 * 2
def baseEnd_840288 : Nat := 383530339738056536031637

theorem tailTrace_840288 : CollatzResearch.WordTrace tailWord_840288 prefixEnd_840288 383530339738056536031637 := by
  unfold tailWord_840288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15323910589893780305056759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20431880786525040406742345 15323910589893780305056759)
  ·
    refine ⟨22985865884840670457585139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15323910589893780305056759 22985865884840670457585139)
    ·
      refine ⟨34478798827261005686377709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22985865884840670457585139 34478798827261005686377709)
      ·
        refine ⟨12929549560222877132391641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34478798827261005686377709 12929549560222877132391641)
        ·
          refine ⟨9697162170167157849293731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12929549560222877132391641 9697162170167157849293731)
          ·
            refine ⟨14545743255250736773940597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9697162170167157849293731 14545743255250736773940597)
            ·
              refine ⟨1363663430179756572556931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14545743255250736773940597 1363663430179756572556931)
              ·
                refine ⟨2045495145269634858835397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363663430179756572556931 2045495145269634858835397)
                ·
                  refine ⟨383530339738056536031637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045495145269634858835397 383530339738056536031637)
                  ·
                    rfl

theorem cell20_840288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_840288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840288 prefixEnd_840288 := by exact prefixLift 840288
  have htrace : WordTrace (prefixWord ++ tailWord_840288) baseStart_840288 baseEnd_840288 := by
    simpa [prefixWord, tailWord_840288, baseEnd_840288] using wordTrace_append hprefix tailTrace_840288
  have hstable : (prefixWord ++ tailWord_840288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840288).length < 2 ^ (prefixWord ++ tailWord_840288).sum := by decide
  have hdescent : baseEnd_840288 < baseStart_840288 := by decide
  rcases family_descends (prefixWord ++ tailWord_840288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840343 : List Nat := [1, 1, 3, 3, 2, 1, 3, 4, 2]
def baseStart_840343 : Nat := 118140960795 + 840343 * 2 ^ 59
def prefixEnd_840343 : Nat := 4983230072969 + 3 ^ 40 * 840343 * 2
def baseEnd_840343 : Nat := 383555443236720789198079

theorem tailTrace_840343 : CollatzResearch.WordTrace tailWord_840343 prefixEnd_840343 383555443236720789198079 := by
  unfold tailWord_840343
  simp only [CollatzResearch.WordTrace]
  refine ⟨30649827194588305003365683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20433218129725536668910455 30649827194588305003365683)
  ·
    refine ⟨45974740791882457505048525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30649827194588305003365683 45974740791882457505048525)
    ·
      refine ⟨17240527796955921564393197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45974740791882457505048525 17240527796955921564393197)
      ·
        refine ⟨6465197923858470586647449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17240527796955921564393197 6465197923858470586647449)
        ·
          refine ⟨4848898442893852939985587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6465197923858470586647449 4848898442893852939985587)
          ·
            refine ⟨7273347664340779409978381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848898442893852939985587 7273347664340779409978381)
            ·
              refine ⟨2727505374127792278741893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7273347664340779409978381 2727505374127792278741893)
              ·
                refine ⟨511407257648961052264105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2727505374127792278741893 511407257648961052264105)
                ·
                  refine ⟨383555443236720789198079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511407257648961052264105 383555443236720789198079)
                  ·
                    rfl

theorem cell20_840343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 2].length) (baseStart_840343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840343 prefixEnd_840343 := by exact prefixLift 840343
  have htrace : WordTrace (prefixWord ++ tailWord_840343) baseStart_840343 baseEnd_840343 := by
    simpa [prefixWord, tailWord_840343, baseEnd_840343] using wordTrace_append hprefix tailTrace_840343
  have hstable : (prefixWord ++ tailWord_840343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840343).length < 2 ^ (prefixWord ++ tailWord_840343).sum := by decide
  have hdescent : baseEnd_840343 < baseStart_840343 := by decide
  rcases family_descends (prefixWord ++ tailWord_840343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840346 : List Nat := [3, 1, 1, 6, 2, 1, 1, 5]
def baseStart_840346 : Nat := 118140960795 + 840346 * 2 ^ 59
def prefixEnd_840346 : Nat := 4983230072969 + 3 ^ 40 * 840346 * 2
def baseEnd_840346 : Nat := 127852270839488704032689

theorem tailTrace_840346 : CollatzResearch.WordTrace tailWord_840346 prefixEnd_840346 127852270839488704032689 := by
  unfold tailWord_840346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662484153394359128931223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20433291075718291010483261 7662484153394359128931223)
  ·
    refine ⟨11493726230091538693396835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7662484153394359128931223 11493726230091538693396835)
    ·
      refine ⟨17240589345137308040095253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11493726230091538693396835 17240589345137308040095253)
      ·
        refine ⟨808152625553311314379465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17240589345137308040095253 808152625553311314379465)
        ·
          refine ⟨606114469164983485784599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808152625553311314379465 606114469164983485784599)
          ·
            refine ⟨909171703747475228676899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606114469164983485784599 909171703747475228676899)
            ·
              refine ⟨1363757555621212843015349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909171703747475228676899 1363757555621212843015349)
              ·
                refine ⟨127852270839488704032689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1363757555621212843015349 127852270839488704032689)
                ·
                  rfl

theorem cell20_840346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_840346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840346 prefixEnd_840346 := by exact prefixLift 840346
  have htrace : WordTrace (prefixWord ++ tailWord_840346) baseStart_840346 baseEnd_840346 := by
    simpa [prefixWord, tailWord_840346, baseEnd_840346] using wordTrace_append hprefix tailTrace_840346
  have hstable : (prefixWord ++ tailWord_840346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840346).length < 2 ^ (prefixWord ++ tailWord_840346).sum := by decide
  have hdescent : baseEnd_840346 < baseStart_840346 := by decide
  rcases family_descends (prefixWord ++ tailWord_840346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840378 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_840378 : Nat := 118140960795 + 840378 * 2 ^ 59
def prefixEnd_840378 : Nat := 4983230072969 + 3 ^ 40 * 840378 * 2
def baseEnd_840378 : Nat := 383571418190416223031269

theorem tailTrace_840378 : CollatzResearch.WordTrace tailWord_840378 prefixEnd_840378 383571418190416223031269 := by
  unfold tailWord_840378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662775937365376495222447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20434069166307670653926525 7662775937365376495222447)
  ·
    refine ⟨11494163906048064742833671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7662775937365376495222447 11494163906048064742833671)
    ·
      refine ⟨17241245859072097114250507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11494163906048064742833671 17241245859072097114250507)
      ·
        refine ⟨25861868788608145671375761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17241245859072097114250507 25861868788608145671375761)
        ·
          refine ⟨19396401591456109253531821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25861868788608145671375761 19396401591456109253531821)
          ·
            refine ⟨7273650596796040970074433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19396401591456109253531821 7273650596796040970074433)
            ·
              refine ⟨5455237947597030727555825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7273650596796040970074433 5455237947597030727555825)
              ·
                refine ⟨4091428460697773045666869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5455237947597030727555825 4091428460697773045666869)
                ·
                  refine ⟨383571418190416223031269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4091428460697773045666869 383571418190416223031269)
                  ·
                    rfl

theorem cell20_840378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_840378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840378 prefixEnd_840378 := by exact prefixLift 840378
  have htrace : WordTrace (prefixWord ++ tailWord_840378) baseStart_840378 baseEnd_840378 := by
    simpa [prefixWord, tailWord_840378, baseEnd_840378] using wordTrace_append hprefix tailTrace_840378
  have hstable : (prefixWord ++ tailWord_840378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840378).length < 2 ^ (prefixWord ++ tailWord_840378).sum := by decide
  have hdescent : baseEnd_840378 < baseStart_840378 := by decide
  rcases family_descends (prefixWord ++ tailWord_840378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840381 : List Nat := [1, 4, 1, 2, 1, 3, 1, 5, 2]
def baseStart_840381 : Nat := 118140960795 + 840381 * 2 ^ 59
def prefixEnd_840381 : Nat := 4983230072969 + 3 ^ 40 * 840381 * 2
def baseEnd_840381 : Nat := 383572787472161545931257

theorem tailTrace_840381 : CollatzResearch.WordTrace tailWord_840381 prefixEnd_840381 383572787472161545931257 := by
  unfold tailWord_840381
  simp only [CollatzResearch.WordTrace]
  refine ⟨30651213168450637493248997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20434142112300424995499331 30651213168450637493248997)
  ·
    refine ⟨5747102469084494529984187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30651213168450637493248997 5747102469084494529984187)
    ·
      refine ⟨8620653703626741794976281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5747102469084494529984187 8620653703626741794976281)
      ·
        refine ⟨6465490277720056346232211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8620653703626741794976281 6465490277720056346232211)
        ·
          refine ⟨9698235416580084519348317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465490277720056346232211 9698235416580084519348317)
          ·
            refine ⟨3636838281217531694755619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9698235416580084519348317 3636838281217531694755619)
            ·
              refine ⟨5455257421826297542133429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636838281217531694755619 5455257421826297542133429)
              ·
                refine ⟨511430383296215394575009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5455257421826297542133429 511430383296215394575009)
                ·
                  refine ⟨383572787472161545931257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511430383296215394575009 383572787472161545931257)
                  ·
                    rfl

theorem cell20_840381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_840381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840381 prefixEnd_840381 := by exact prefixLift 840381
  have htrace : WordTrace (prefixWord ++ tailWord_840381) baseStart_840381 baseEnd_840381 := by
    simpa [prefixWord, tailWord_840381, baseEnd_840381] using wordTrace_append hprefix tailTrace_840381
  have hstable : (prefixWord ++ tailWord_840381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840381).length < 2 ^ (prefixWord ++ tailWord_840381).sum := by decide
  have hdescent : baseEnd_840381 < baseStart_840381 := by decide
  rcases family_descends (prefixWord ++ tailWord_840381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840502 : List Nat := [5, 1, 2, 2, 2, 8]
def baseStart_840502 : Nat := 118140960795 + 840502 * 2 ^ 59
def prefixEnd_840502 : Nat := 4983230072969 + 3 ^ 40 * 840502 * 2
def baseEnd_840502 : Nat := 14208445006267514922127

theorem tailTrace_840502 : CollatzResearch.WordTrace tailWord_840502 prefixEnd_840502 14208445006267514922127 := by
  unfold tailWord_840502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915976650063267197400235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20437084267341516772269173 1915976650063267197400235)
  ·
    refine ⟨2873964975094900796100353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1915976650063267197400235 2873964975094900796100353)
    ·
      refine ⟨2155473731321175597075265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2873964975094900796100353 2155473731321175597075265)
      ·
        refine ⟨1616605298490881697806449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2155473731321175597075265 1616605298490881697806449)
        ·
          refine ⟨1212453973868161273354837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1616605298490881697806449 1212453973868161273354837)
          ·
            refine ⟨14208445006267514922127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1212453973868161273354837 14208445006267514922127)
            ·
              rfl

theorem cell20_840502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 8].length) (baseStart_840502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840502 prefixEnd_840502 := by exact prefixLift 840502
  have htrace : WordTrace (prefixWord ++ tailWord_840502) baseStart_840502 baseEnd_840502 := by
    simpa [prefixWord, tailWord_840502, baseEnd_840502] using wordTrace_append hprefix tailTrace_840502
  have hstable : (prefixWord ++ tailWord_840502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840502).length < 2 ^ (prefixWord ++ tailWord_840502).sum := by decide
  have hdescent : baseEnd_840502 < baseStart_840502 := by decide
  rcases family_descends (prefixWord ++ tailWord_840502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840506 : List Nat := [3, 1, 1, 1, 14]
def baseStart_840506 : Nat := 118140960795 + 840506 * 2 ^ 59
def prefixEnd_840506 : Nat := 4983230072969 + 3 ^ 40 * 840506 * 2
def baseEnd_840506 : Nat := 4736170875039711935359

theorem tailTrace_840506 : CollatzResearch.WordTrace tailWord_840506 prefixEnd_840506 4736170875039711935359 := by
  unfold tailWord_840506
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663943073249445960387343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20437181528665189227699581 7663943073249445960387343)
  ·
    refine ⟨11495914609874168940581015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7663943073249445960387343 11495914609874168940581015)
    ·
      refine ⟨17243871914811253410871523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11495914609874168940581015 17243871914811253410871523)
      ·
        refine ⟨25865807872216880116307285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17243871914811253410871523 25865807872216880116307285)
        ·
          refine ⟨4736170875039711935359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 25865807872216880116307285 4736170875039711935359)
          ·
            rfl

theorem cell20_840506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 14].length) (baseStart_840506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840506 prefixEnd_840506 := by exact prefixLift 840506
  have htrace : WordTrace (prefixWord ++ tailWord_840506) baseStart_840506 baseEnd_840506 := by
    simpa [prefixWord, tailWord_840506, baseEnd_840506] using wordTrace_append hprefix tailTrace_840506
  have hstable : (prefixWord ++ tailWord_840506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840506).length < 2 ^ (prefixWord ++ tailWord_840506).sum := by decide
  have hdescent : baseEnd_840506 < baseStart_840506 := by decide
  rcases family_descends (prefixWord ++ tailWord_840506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840537 : List Nat := [1, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_840537 : Nat := 118140960795 + 840537 * 2 ^ 59
def prefixEnd_840537 : Nat := 4983230072969 + 3 ^ 40 * 840537 * 2
def baseEnd_840537 : Nat := 383643990122918336730619

theorem tailTrace_840537 : CollatzResearch.WordTrace tailWord_840537 prefixEnd_840537 383643990122918336730619 := by
  unfold tailWord_840537
  simp only [CollatzResearch.WordTrace]
  refine ⟨30656902955885476135927865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20437935303923650757285243 30656902955885476135927865)
  ·
    refine ⟨22992677216914107101945899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30656902955885476135927865 22992677216914107101945899)
    ·
      refine ⟨34489015825371160652918849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22992677216914107101945899 34489015825371160652918849)
      ·
        refine ⟨25866761869028370489689137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34489015825371160652918849 25866761869028370489689137)
        ·
          refine ⟨19400071401771277867266853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25866761869028370489689137 19400071401771277867266853)
          ·
            refine ⟨3637513387832114600112535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19400071401771277867266853 3637513387832114600112535)
            ·
              refine ⟨5456270081748171900168803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3637513387832114600112535 5456270081748171900168803)
              ·
                refine ⟨8184405122622257850253205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5456270081748171900168803 8184405122622257850253205)
                ·
                  refine ⟨383643990122918336730619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8184405122622257850253205 383643990122918336730619)
                  ·
                    rfl

theorem cell20_840537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_840537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840537 prefixEnd_840537 := by exact prefixLift 840537
  have htrace : WordTrace (prefixWord ++ tailWord_840537) baseStart_840537 baseEnd_840537 := by
    simpa [prefixWord, tailWord_840537, baseEnd_840537] using wordTrace_append hprefix tailTrace_840537
  have hstable : (prefixWord ++ tailWord_840537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840537).length < 2 ^ (prefixWord ++ tailWord_840537).sum := by decide
  have hdescent : baseEnd_840537 < baseStart_840537 := by decide
  rcases family_descends (prefixWord ++ tailWord_840537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840568 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_840568 : Nat := 118140960795 + 840568 * 2 ^ 59
def prefixEnd_840568 : Nat := 4983230072969 + 3 ^ 40 * 840568 * 2
def baseEnd_840568 : Nat := 383658139367620006697159

theorem tailTrace_840568 : CollatzResearch.WordTrace tailWord_840568 prefixEnd_840568 383658139367620006697159 := by
  unfold tailWord_840568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15329016809386584215153179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20438689079182112286870905 15329016809386584215153179)
  ·
    refine ⟨22993525214079876322729769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15329016809386584215153179 22993525214079876322729769)
    ·
      refine ⟨17245143910559907242047327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22993525214079876322729769 17245143910559907242047327)
      ·
        refine ⟨25867715865839860863070991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17245143910559907242047327 25867715865839860863070991)
        ·
          refine ⟨38801573798759791294606487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25867715865839860863070991 38801573798759791294606487)
          ·
            refine ⟨58202360698139686941909731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38801573798759791294606487 58202360698139686941909731)
            ·
              refine ⟨87303541047209530412864597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58202360698139686941909731 87303541047209530412864597)
              ·
                refine ⟨1023088371646986684525757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 87303541047209530412864597 1023088371646986684525757)
                ·
                  refine ⟨383658139367620006697159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023088371646986684525757 383658139367620006697159)
                  ·
                    rfl

theorem cell20_840568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_840568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840568 prefixEnd_840568 := by exact prefixLift 840568
  have htrace : WordTrace (prefixWord ++ tailWord_840568) baseStart_840568 baseEnd_840568 := by
    simpa [prefixWord, tailWord_840568, baseEnd_840568] using wordTrace_append hprefix tailTrace_840568
  have hstable : (prefixWord ++ tailWord_840568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840568).length < 2 ^ (prefixWord ++ tailWord_840568).sum := by decide
  have hdescent : baseEnd_840568 < baseStart_840568 := by decide
  rcases family_descends (prefixWord ++ tailWord_840568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840575 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 4]
def baseStart_840575 : Nat := 118140960795 + 840575 * 2 ^ 59
def prefixEnd_840575 : Nat := 4983230072969 + 3 ^ 40 * 840575 * 2
def baseEnd_840575 : Nat := 383661334358359093463797

theorem tailTrace_840575 : CollatzResearch.WordTrace tailWord_840575 prefixEnd_840575 383661334358359093463797 := by
  unfold tailWord_840575
  simp only [CollatzResearch.WordTrace]
  refine ⟨30658288929747808625811179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20438859286498539083874119 30658288929747808625811179)
  ·
    refine ⟨45987433394621712938716769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30658288929747808625811179 45987433394621712938716769)
    ·
      refine ⟨34490575045966284704037577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45987433394621712938716769 34490575045966284704037577)
      ·
        refine ⟨25867931284474713528028183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34490575045966284704037577 25867931284474713528028183)
        ·
          refine ⟨38801896926712070292042275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25867931284474713528028183 38801896926712070292042275)
          ·
            refine ⟨58202845390068105438063413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38801896926712070292042275 58202845390068105438063413)
            ·
              refine ⟨5456516755318884884818445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58202845390068105438063413 5456516755318884884818445)
              ·
                refine ⟨2046193783244581831806917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5456516755318884884818445 2046193783244581831806917)
                ·
                  refine ⟨383661334358359093463797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2046193783244581831806917 383661334358359093463797)
                  ·
                    rfl

theorem cell20_840575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_840575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840575 prefixEnd_840575 := by exact prefixLift 840575
  have htrace : WordTrace (prefixWord ++ tailWord_840575) baseStart_840575 baseEnd_840575 := by
    simpa [prefixWord, tailWord_840575, baseEnd_840575] using wordTrace_append hprefix tailTrace_840575
  have hstable : (prefixWord ++ tailWord_840575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840575).length < 2 ^ (prefixWord ++ tailWord_840575).sum := by decide
  have hdescent : baseEnd_840575 < baseStart_840575 := by decide
  rcases family_descends (prefixWord ++ tailWord_840575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840640 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 3]
def baseStart_840640 : Nat := 118140960795 + 840640 * 2 ^ 59
def prefixEnd_840640 : Nat := 4983230072969 + 3 ^ 40 * 840640 * 2
def baseEnd_840640 : Nat := 383691002129507756296865

theorem tailTrace_840640 : CollatzResearch.WordTrace tailWord_840640 prefixEnd_840640 383691002129507756296865 := by
  unfold tailWord_840640
  simp only [CollatzResearch.WordTrace]
  refine ⟨15330329837256162363463687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20440439783008216484618249 15330329837256162363463687)
  ·
    refine ⟨22995494755884243545195531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15330329837256162363463687 22995494755884243545195531)
    ·
      refine ⟨34493242133826365317793297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22995494755884243545195531 34493242133826365317793297)
      ·
        refine ⟨25869931600369773988344973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34493242133826365317793297 25869931600369773988344973)
        ·
          refine ⟨9701224350138665245629365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25869931600369773988344973 9701224350138665245629365)
          ·
            refine ⟨909489782825499866777753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9701224350138665245629365 909489782825499866777753)
            ·
              refine ⟨682117337119124900083315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909489782825499866777753 682117337119124900083315)
              ·
                refine ⟨1023176005678687350124973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682117337119124900083315 1023176005678687350124973)
                ·
                  refine ⟨383691002129507756296865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023176005678687350124973 383691002129507756296865)
                  ·
                    rfl

theorem cell20_840640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_840640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840640 prefixEnd_840640 := by exact prefixLift 840640
  have htrace : WordTrace (prefixWord ++ tailWord_840640) baseStart_840640 baseEnd_840640 := by
    simpa [prefixWord, tailWord_840640, baseEnd_840640] using wordTrace_append hprefix tailTrace_840640
  have hstable : (prefixWord ++ tailWord_840640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840640).length < 2 ^ (prefixWord ++ tailWord_840640).sum := by decide
  have hdescent : baseEnd_840640 < baseStart_840640 := by decide
  rcases family_descends (prefixWord ++ tailWord_840640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840703 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_840703 : Nat := 118140960795 + 840703 * 2 ^ 59
def prefixEnd_840703 : Nat := 4983230072969 + 3 ^ 40 * 840703 * 2
def baseEnd_840703 : Nat := 383719757046159537196607

theorem tailTrace_840703 : CollatzResearch.WordTrace tailWord_840703 prefixEnd_840703 383719757046159537196607 := by
  unfold tailWord_840703
  simp only [CollatzResearch.WordTrace]
  refine ⟨30662957473284086486470763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20441971648856057657647175 30662957473284086486470763)
  ·
    refine ⟨45994436209926129729706145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30662957473284086486470763 45994436209926129729706145)
    ·
      refine ⟨34495827157444597297279609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45994436209926129729706145 34495827157444597297279609)
      ·
        refine ⟨25871870368083447972959707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34495827157444597297279609 25871870368083447972959707)
        ·
          refine ⟨38807805552125171959439561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25871870368083447972959707 38807805552125171959439561)
          ·
            refine ⟨29105854164093878969579671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38807805552125171959439561 29105854164093878969579671)
            ·
              refine ⟨43658781246140818454369507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29105854164093878969579671 43658781246140818454369507)
              ·
                refine ⟨65488171869211227681554261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43658781246140818454369507 65488171869211227681554261)
                ·
                  refine ⟨383719757046159537196607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65488171869211227681554261 383719757046159537196607)
                  ·
                    rfl

theorem cell20_840703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_840703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840703 prefixEnd_840703 := by exact prefixLift 840703
  have htrace : WordTrace (prefixWord ++ tailWord_840703) baseStart_840703 baseEnd_840703 := by
    simpa [prefixWord, tailWord_840703, baseEnd_840703] using wordTrace_append hprefix tailTrace_840703
  have hstable : (prefixWord ++ tailWord_840703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840703).length < 2 ^ (prefixWord ++ tailWord_840703).sum := by decide
  have hdescent : baseEnd_840703 < baseStart_840703 := by decide
  rcases family_descends (prefixWord ++ tailWord_840703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840733 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 3]
def baseStart_840733 : Nat := 118140960795 + 840733 * 2 ^ 59
def prefixEnd_840733 : Nat := 4983230072969 + 3 ^ 40 * 840733 * 2
def baseEnd_840733 : Nat := 383733449863612766196485

theorem tailTrace_840733 : CollatzResearch.WordTrace tailWord_840733 prefixEnd_840733 383733449863612766196485 := by
  unfold tailWord_840733
  simp only [CollatzResearch.WordTrace]
  refine ⟨30664051663175401610062853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20442701108783601073375235 30664051663175401610062853)
  ·
    refine ⟨5749509686845387801886785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30664051663175401610062853 5749509686845387801886785)
    ·
      refine ⟨4312132265134040851415089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5749509686845387801886785 4312132265134040851415089)
      ·
        refine ⟨3234099198850530638561317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4312132265134040851415089 3234099198850530638561317)
        ·
          refine ⟨606393599784474494730247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3234099198850530638561317 606393599784474494730247)
          ·
            refine ⟨909590399676711742095371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606393599784474494730247 909590399676711742095371)
            ·
              refine ⟨1364385599515067613143057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909590399676711742095371 1364385599515067613143057)
              ·
                refine ⟨1023289199636300709857293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364385599515067613143057 1023289199636300709857293)
                ·
                  refine ⟨383733449863612766196485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023289199636300709857293 383733449863612766196485)
                  ·
                    rfl

theorem cell20_840733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_840733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840733 prefixEnd_840733 := by exact prefixLift 840733
  have htrace : WordTrace (prefixWord ++ tailWord_840733) baseStart_840733 baseEnd_840733 := by
    simpa [prefixWord, tailWord_840733, baseEnd_840733] using wordTrace_append hprefix tailTrace_840733
  have hstable : (prefixWord ++ tailWord_840733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840733).length < 2 ^ (prefixWord ++ tailWord_840733).sum := by decide
  have hdescent : baseEnd_840733 < baseStart_840733 := by decide
  rcases family_descends (prefixWord ++ tailWord_840733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840737 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 3]
def baseStart_840737 : Nat := 118140960795 + 840737 * 2 ^ 59
def prefixEnd_840737 : Nat := 4983230072969 + 3 ^ 40 * 840737 * 2
def baseEnd_840737 : Nat := 383735275572606530063135

theorem tailTrace_840737 : CollatzResearch.WordTrace tailWord_840737 prefixEnd_840737 383735275572606530063135 := by
  unfold tailWord_840737
  simp only [CollatzResearch.WordTrace]
  refine ⟨30664197555160910293208465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20442798370107273528805643 30664197555160910293208465)
  ·
    refine ⟨22998148166370682719906349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30664197555160910293208465 22998148166370682719906349)
    ·
      refine ⟨8624305562389006019964881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22998148166370682719906349 8624305562389006019964881)
      ·
        refine ⟨6468229171791754514973661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8624305562389006019964881 6468229171791754514973661)
        ·
          refine ⟨2425585939421907943115123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6468229171791754514973661 2425585939421907943115123)
          ·
            refine ⟨3638378909132861914672685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425585939421907943115123 3638378909132861914672685)
            ·
              refine ⟨1364392090924823218002257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3638378909132861914672685 1364392090924823218002257)
              ·
                refine ⟨1023294068193617413501693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364392090924823218002257 1023294068193617413501693)
                ·
                  refine ⟨383735275572606530063135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023294068193617413501693 383735275572606530063135)
                  ·
                    rfl

theorem cell20_840737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_840737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840737 prefixEnd_840737 := by exact prefixLift 840737
  have htrace : WordTrace (prefixWord ++ tailWord_840737) baseStart_840737 baseEnd_840737 := by
    simpa [prefixWord, tailWord_840737, baseEnd_840737] using wordTrace_append hprefix tailTrace_840737
  have hstable : (prefixWord ++ tailWord_840737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840737).length < 2 ^ (prefixWord ++ tailWord_840737).sum := by decide
  have hdescent : baseEnd_840737 < baseStart_840737 := by decide
  rcases family_descends (prefixWord ++ tailWord_840737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840796 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_840796 : Nat := 118140960795 + 840796 * 2 ^ 59
def prefixEnd_840796 : Nat := 4983230072969 + 3 ^ 40 * 840796 * 2
def baseEnd_840796 : Nat := 383762204780264547096227

theorem tailTrace_840796 : CollatzResearch.WordTrace tailWord_840796 prefixEnd_840796 383762204780264547096227 := by
  unfold tailWord_840796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15333174730973581684803121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20444232974631442246404161 15333174730973581684803121)
  ·
    refine ⟨11499881048230186263602341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15333174730973581684803121 11499881048230186263602341)
    ·
      refine ⟨2156227696543159924425439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11499881048230186263602341 2156227696543159924425439)
      ·
        refine ⟨3234341544814739886638159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156227696543159924425439 3234341544814739886638159)
        ·
          refine ⟨4851512317222109829957239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234341544814739886638159 4851512317222109829957239)
          ·
            refine ⟨7277268475833164744935859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4851512317222109829957239 7277268475833164744935859)
            ·
              refine ⟨10915902713749747117403789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7277268475833164744935859 10915902713749747117403789)
              ·
                refine ⟨4093463517656155169026421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10915902713749747117403789 4093463517656155169026421)
                ·
                  refine ⟨383762204780264547096227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4093463517656155169026421 383762204780264547096227)
                  ·
                    rfl

theorem cell20_840796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_840796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840796 prefixEnd_840796 := by exact prefixLift 840796
  have htrace : WordTrace (prefixWord ++ tailWord_840796) baseStart_840796 baseEnd_840796 := by
    simpa [prefixWord, tailWord_840796, baseEnd_840796] using wordTrace_append hprefix tailTrace_840796
  have hstable : (prefixWord ++ tailWord_840796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840796).length < 2 ^ (prefixWord ++ tailWord_840796).sum := by decide
  have hdescent : baseEnd_840796 < baseStart_840796 := by decide
  rcases family_descends (prefixWord ++ tailWord_840796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840799 : List Nat := [1, 1, 2, 3, 1, 1, 7, 2, 2]
def baseStart_840799 : Nat := 118140960795 + 840799 * 2 ^ 59
def prefixEnd_840799 : Nat := 4983230072969 + 3 ^ 40 * 840799 * 2
def baseEnd_840799 : Nat := 383763574062009869996215

theorem tailTrace_840799 : CollatzResearch.WordTrace tailWord_840799 prefixEnd_840799 383763574062009869996215 := by
  unfold tailWord_840799
  simp only [CollatzResearch.WordTrace]
  refine ⟨30666458880936294881965451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20444305920624196587976967 30666458880936294881965451)
  ·
    refine ⟨45999688321404442322948177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30666458880936294881965451 45999688321404442322948177)
    ·
      refine ⟨34499766241053331742211133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45999688321404442322948177 34499766241053331742211133)
      ·
        refine ⟨12937412340394999403329175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34499766241053331742211133 12937412340394999403329175)
        ·
          refine ⟨19406118510592499104993763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12937412340394999403329175 19406118510592499104993763)
          ·
            refine ⟨29109177765888748657490645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19406118510592499104993763 29109177765888748657490645)
            ·
              refine ⟨682246353888017546659937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29109177765888748657490645 682246353888017546659937)
              ·
                refine ⟨511684765416013159994953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682246353888017546659937 511684765416013159994953)
                ·
                  refine ⟨383763574062009869996215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511684765416013159994953 383763574062009869996215)
                  ·
                    rfl

theorem cell20_840799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 2].length) (baseStart_840799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840799 prefixEnd_840799 := by exact prefixLift 840799
  have htrace : WordTrace (prefixWord ++ tailWord_840799) baseStart_840799 baseEnd_840799 := by
    simpa [prefixWord, tailWord_840799, baseEnd_840799] using wordTrace_append hprefix tailTrace_840799
  have hstable : (prefixWord ++ tailWord_840799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840799).length < 2 ^ (prefixWord ++ tailWord_840799).sum := by decide
  have hdescent : baseEnd_840799 < baseStart_840799 := by decide
  rcases family_descends (prefixWord ++ tailWord_840799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840813 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 3]
def baseStart_840813 : Nat := 118140960795 + 840813 * 2 ^ 59
def prefixEnd_840813 : Nat := 4983230072969 + 3 ^ 40 * 840813 * 2
def baseEnd_840813 : Nat := 383769964043488043529491

theorem tailTrace_840813 : CollatzResearch.WordTrace tailWord_840813 prefixEnd_840813 383769964043488043529491 := by
  unfold tailWord_840813
  simp only [CollatzResearch.WordTrace]
  refine ⟨30666969502885575272975093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20444646335257050181983395 30666969502885575272975093)
  ·
    refine ⟨2875028390895522681841415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30666969502885575272975093 2875028390895522681841415)
    ·
      refine ⟨4312542586343284022762123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2875028390895522681841415 4312542586343284022762123)
      ·
        refine ⟨6468813879514926034143185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312542586343284022762123 6468813879514926034143185)
        ·
          refine ⟨4851610409636194525607389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6468813879514926034143185 4851610409636194525607389)
          ·
            refine ⟨1819353903613572947102771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4851610409636194525607389 1819353903613572947102771)
            ·
              refine ⟨2729030855420359420654157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819353903613572947102771 2729030855420359420654157)
              ·
                refine ⟨1023386570782634782745309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2729030855420359420654157 1023386570782634782745309)
                ·
                  refine ⟨383769964043488043529491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023386570782634782745309 383769964043488043529491)
                  ·
                    rfl

theorem cell20_840813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_840813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840813 prefixEnd_840813 := by exact prefixLift 840813
  have htrace : WordTrace (prefixWord ++ tailWord_840813) baseStart_840813 baseEnd_840813 := by
    simpa [prefixWord, tailWord_840813, baseEnd_840813] using wordTrace_append hprefix tailTrace_840813
  have hstable : (prefixWord ++ tailWord_840813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840813).length < 2 ^ (prefixWord ++ tailWord_840813).sum := by decide
  have hdescent : baseEnd_840813 < baseStart_840813 := by decide
  rcases family_descends (prefixWord ++ tailWord_840813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840817 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_840817 : Nat := 118140960795 + 840817 * 2 ^ 59
def prefixEnd_840817 : Nat := 4983230072969 + 3 ^ 40 * 840817 * 2
def baseEnd_840817 : Nat := 383771789752481807396141

theorem tailTrace_840817 : CollatzResearch.WordTrace tailWord_840817 prefixEnd_840817 383771789752481807396141 := by
  unfold tailWord_840817
  simp only [CollatzResearch.WordTrace]
  refine ⟨30667115394871083956120705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20444743596580722637413803 30667115394871083956120705)
  ·
    refine ⟨23000336546153312967090529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30667115394871083956120705 23000336546153312967090529)
    ·
      refine ⟨17250252409614984725317897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23000336546153312967090529 17250252409614984725317897)
      ·
        refine ⟨12937689307211238543988423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17250252409614984725317897 12937689307211238543988423)
        ·
          refine ⟨19406533960816857815982635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12937689307211238543988423 19406533960816857815982635)
          ·
            refine ⟨29109800941225286723973953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19406533960816857815982635 29109800941225286723973953)
            ·
              refine ⟨21832350705918965042980465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29109800941225286723973953 21832350705918965042980465)
              ·
                refine ⟨16374263029439223782235349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21832350705918965042980465 16374263029439223782235349)
                ·
                  refine ⟨383771789752481807396141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16374263029439223782235349 383771789752481807396141)
                  ·
                    rfl

theorem cell20_840817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_840817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840817 prefixEnd_840817 := by exact prefixLift 840817
  have htrace : WordTrace (prefixWord ++ tailWord_840817) baseStart_840817 baseEnd_840817 := by
    simpa [prefixWord, tailWord_840817, baseEnd_840817] using wordTrace_append hprefix tailTrace_840817
  have hstable : (prefixWord ++ tailWord_840817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840817).length < 2 ^ (prefixWord ++ tailWord_840817).sum := by decide
  have hdescent : baseEnd_840817 < baseStart_840817 := by decide
  rcases family_descends (prefixWord ++ tailWord_840817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840941 : List Nat := [1, 5, 1, 2, 2, 2, 1, 6]
def baseStart_840941 : Nat := 118140960795 + 840941 * 2 ^ 59
def prefixEnd_840941 : Nat := 4983230072969 + 3 ^ 40 * 840941 * 2
def baseEnd_840941 : Nat := 127942795577096162420767

theorem tailTrace_840941 : CollatzResearch.WordTrace tailWord_840941 prefixEnd_840941 127942795577096162420767 := by
  unfold tailWord_840941
  simp only [CollatzResearch.WordTrace]
  refine ⟨30671638046421853133634677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20447758697614568755756451 30671638046421853133634677)
  ·
    refine ⟨2875466066852048731278251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30671638046421853133634677 2875466066852048731278251)
    ·
      refine ⟨4313199100278073096917377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2875466066852048731278251 4313199100278073096917377)
      ·
        refine ⟨3234899325208554822688033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4313199100278073096917377 3234899325208554822688033)
        ·
          refine ⟨2426174493906416117016025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3234899325208554822688033 2426174493906416117016025)
          ·
            refine ⟨1819630870429812087762019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426174493906416117016025 1819630870429812087762019)
            ·
              refine ⟨2729446305644718131643029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819630870429812087762019 2729446305644718131643029)
              ·
                refine ⟨127942795577096162420767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2729446305644718131643029 127942795577096162420767)
                ·
                  rfl

theorem cell20_840941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_840941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840941 prefixEnd_840941 := by exact prefixLift 840941
  have htrace : WordTrace (prefixWord ++ tailWord_840941) baseStart_840941 baseEnd_840941 := by
    simpa [prefixWord, tailWord_840941, baseEnd_840941] using wordTrace_append hprefix tailTrace_840941
  have hstable : (prefixWord ++ tailWord_840941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840941).length < 2 ^ (prefixWord ++ tailWord_840941).sum := by decide
  have hdescent : baseEnd_840941 < baseStart_840941 := by decide
  rcases family_descends (prefixWord ++ tailWord_840941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840968 : List Nat := [2, 1, 3, 2, 4, 1, 3, 2, 2]
def baseStart_840968 : Nat := 118140960795 + 840968 * 2 ^ 59
def prefixEnd_840968 : Nat := 4983230072969 + 3 ^ 40 * 840968 * 2
def baseEnd_840968 : Nat := 383840710266996393362191

theorem tailTrace_840968 : CollatzResearch.WordTrace tailWord_840968 prefixEnd_840968 383840710266996393362191 := by
  unfold tailWord_840968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15336311408662018372433779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20448415211549357829911705 15336311408662018372433779)
  ·
    refine ⟨23004467112993027558650669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15336311408662018372433779 23004467112993027558650669)
    ·
      refine ⟨8626675167372385334494001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23004467112993027558650669 8626675167372385334494001)
      ·
        refine ⟨6470006375529289000870501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8626675167372385334494001 6470006375529289000870501)
        ·
          refine ⟨1213126195411741687663219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6470006375529289000870501 1213126195411741687663219)
          ·
            refine ⟨1819689293117612531494829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213126195411741687663219 1819689293117612531494829)
            ·
              refine ⟨682383484919104699310561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1819689293117612531494829 682383484919104699310561)
              ·
                refine ⟨511787613689328524482921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682383484919104699310561 511787613689328524482921)
                ·
                  refine ⟨383840710266996393362191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511787613689328524482921 383840710266996393362191)
                  ·
                    rfl

theorem cell20_840968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 2].length) (baseStart_840968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840968 prefixEnd_840968 := by exact prefixLift 840968
  have htrace : WordTrace (prefixWord ++ tailWord_840968) baseStart_840968 baseEnd_840968 := by
    simpa [prefixWord, tailWord_840968, baseEnd_840968] using wordTrace_append hprefix tailTrace_840968
  have hstable : (prefixWord ++ tailWord_840968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840968).length < 2 ^ (prefixWord ++ tailWord_840968).sum := by decide
  have hdescent : baseEnd_840968 < baseStart_840968 := by decide
  rcases family_descends (prefixWord ++ tailWord_840968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840969 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_840969 : Nat := 118140960795 + 840969 * 2 ^ 59
def prefixEnd_840969 : Nat := 4983230072969 + 3 ^ 40 * 840969 * 2
def baseEnd_840969 : Nat := 383841166694244834328853

theorem tailTrace_840969 : CollatzResearch.WordTrace tailWord_840969 prefixEnd_840969 383841166694244834328853 := by
  unfold tailWord_840969
  simp only [CollatzResearch.WordTrace]
  refine ⟨30672659290320413915653961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20448439526880275943769307 30672659290320413915653961)
  ·
    refine ⟨23004494467740310436740471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30672659290320413915653961 23004494467740310436740471)
    ·
      refine ⟨34506741701610465655110707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23004494467740310436740471 34506741701610465655110707)
      ·
        refine ⟨51760112552415698482666061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34506741701610465655110707 51760112552415698482666061)
        ·
          refine ⟨19410042207155886930999773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51760112552415698482666061 19410042207155886930999773)
          ·
            refine ⟨7278765827683457599124915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19410042207155886930999773 7278765827683457599124915)
            ·
              refine ⟨10918148741525186398687373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278765827683457599124915 10918148741525186398687373)
              ·
                refine ⟨4094305778071944899507765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10918148741525186398687373 4094305778071944899507765)
                ·
                  refine ⟨383841166694244834328853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4094305778071944899507765 383841166694244834328853)
                  ·
                    rfl

theorem cell20_840969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_840969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840969 prefixEnd_840969 := by exact prefixLift 840969
  have htrace : WordTrace (prefixWord ++ tailWord_840969) baseStart_840969 baseEnd_840969 := by
    simpa [prefixWord, tailWord_840969, baseEnd_840969] using wordTrace_append hprefix tailTrace_840969
  have hstable : (prefixWord ++ tailWord_840969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840969).length < 2 ^ (prefixWord ++ tailWord_840969).sum := by decide
  have hdescent : baseEnd_840969 < baseStart_840969 := by decide
  rcases family_descends (prefixWord ++ tailWord_840969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840972 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 4]
def baseStart_840972 : Nat := 118140960795 + 840972 * 2 ^ 59
def prefixEnd_840972 : Nat := 4983230072969 + 3 ^ 40 * 840972 * 2
def baseEnd_840972 : Nat := 383842535975990157228841

theorem tailTrace_840972 : CollatzResearch.WordTrace tailWord_840972 prefixEnd_840972 383842535975990157228841 := by
  unfold tailWord_840972
  simp only [CollatzResearch.WordTrace]
  refine ⟨15336384354654772714006585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20448512472873030285342113 15336384354654772714006585)
  ·
    refine ⟨11502288265991079535504939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15336384354654772714006585 11502288265991079535504939)
    ·
      refine ⟨17253432398986619303257409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11502288265991079535504939 17253432398986619303257409)
      ·
        refine ⟨12940074299239964477443057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17253432398986619303257409 12940074299239964477443057)
        ·
          refine ⟨9705055724429973358082293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12940074299239964477443057 9705055724429973358082293)
          ·
            refine ⟨909848974165310002320215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9705055724429973358082293 909848974165310002320215)
            ·
              refine ⟨1364773461247965003480323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909848974165310002320215 1364773461247965003480323)
              ·
                refine ⟨2047160191871947505220485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364773461247965003480323 2047160191871947505220485)
                ·
                  refine ⟨383842535975990157228841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2047160191871947505220485 383842535975990157228841)
                  ·
                    rfl

theorem cell20_840972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_840972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840972 prefixEnd_840972 := by exact prefixLift 840972
  have htrace : WordTrace (prefixWord ++ tailWord_840972) baseStart_840972 baseEnd_840972 := by
    simpa [prefixWord, tailWord_840972, baseEnd_840972] using wordTrace_append hprefix tailTrace_840972
  have hstable : (prefixWord ++ tailWord_840972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840972).length < 2 ^ (prefixWord ++ tailWord_840972).sum := by decide
  have hdescent : baseEnd_840972 < baseStart_840972 := by decide
  rcases family_descends (prefixWord ++ tailWord_840972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_840978 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_840978 : Nat := 118140960795 + 840978 * 2 ^ 59
def prefixEnd_840978 : Nat := 4983230072969 + 3 ^ 40 * 840978 * 2
def baseEnd_840978 : Nat := 383845274539480803028817

theorem tailTrace_840978 : CollatzResearch.WordTrace tailWord_840978 prefixEnd_840978 383845274539480803028817 := by
  unfold tailWord_840978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668246886821952113182897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20448658364858538968487725 7668246886821952113182897)
  ·
    refine ⟨5751185165116464084887173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7668246886821952113182897 5751185165116464084887173)
    ·
      refine ⟨1078347218459337015916345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5751185165116464084887173 1078347218459337015916345)
      ·
        refine ⟨808760413844502761937259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1078347218459337015916345 808760413844502761937259)
        ·
          refine ⟨1213140620766754142905889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808760413844502761937259 1213140620766754142905889)
          ·
            refine ⟨909855465575065607179417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213140620766754142905889 909855465575065607179417)
            ·
              refine ⟨682391599181299205384563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909855465575065607179417 682391599181299205384563)
              ·
                refine ⟨1023587398771948808076845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682391599181299205384563 1023587398771948808076845)
                ·
                  refine ⟨383845274539480803028817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023587398771948808076845 383845274539480803028817)
                  ·
                    rfl

theorem cell20_840978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_840978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_840978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_840978 prefixEnd_840978 := by exact prefixLift 840978
  have htrace : WordTrace (prefixWord ++ tailWord_840978) baseStart_840978 baseEnd_840978 := by
    simpa [prefixWord, tailWord_840978, baseEnd_840978] using wordTrace_append hprefix tailTrace_840978
  have hstable : (prefixWord ++ tailWord_840978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_840978).length < 2 ^ (prefixWord ++ tailWord_840978).sum := by decide
  have hdescent : baseEnd_840978 < baseStart_840978 := by decide
  rcases family_descends (prefixWord ++ tailWord_840978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841017 : List Nat := [1, 2, 1, 6, 3, 7]
def baseStart_841017 : Nat := 118140960795 + 841017 * 2 ^ 59
def prefixEnd_841017 : Nat := 4983230072969 + 3 ^ 40 * 841017 * 2
def baseEnd_841017 : Nat := 14217150933413703730691

theorem tailTrace_841017 : CollatzResearch.WordTrace tailWord_841017 prefixEnd_841017 14217150933413703730691 := by
  unfold tailWord_841017
  simp only [CollatzResearch.WordTrace]
  refine ⟨30674409994146518113401305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20449606662764345408934203 30674409994146518113401305)
  ·
    refine ⟨23005807495609888585050979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30674409994146518113401305 23005807495609888585050979)
    ·
      refine ⟨34508711243414832877576469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23005807495609888585050979 34508711243414832877576469)
      ·
        refine ⟨1617595839535070291136397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34508711243414832877576469 1617595839535070291136397)
        ·
          refine ⟨606598439825651359176149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1617595839535070291136397 606598439825651359176149)
          ·
            refine ⟨14217150933413703730691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 606598439825651359176149 14217150933413703730691)
            ·
              rfl

theorem cell20_841017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 7].length) (baseStart_841017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841017 prefixEnd_841017 := by exact prefixLift 841017
  have htrace : WordTrace (prefixWord ++ tailWord_841017) baseStart_841017 baseEnd_841017 := by
    simpa [prefixWord, tailWord_841017, baseEnd_841017] using wordTrace_append hprefix tailTrace_841017
  have hstable : (prefixWord ++ tailWord_841017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841017).length < 2 ^ (prefixWord ++ tailWord_841017).sum := by decide
  have hdescent : baseEnd_841017 < baseStart_841017 := by decide
  rcases family_descends (prefixWord ++ tailWord_841017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841024 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_841024 : Nat := 118140960795 + 841024 * 2 ^ 59
def prefixEnd_841024 : Nat := 4983230072969 + 3 ^ 40 * 841024 * 2
def baseEnd_841024 : Nat := 383866270192909087495295

theorem tailTrace_841024 : CollatzResearch.WordTrace tailWord_841024 prefixEnd_841024 383866270192909087495295 := by
  unfold tailWord_841024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15337332652560579154453063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20449776870080772205937417 15337332652560579154453063)
  ·
    refine ⟨23005998978840868731679595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15337332652560579154453063 23005998978840868731679595)
    ·
      refine ⟨34508998468261303097519393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23005998978840868731679595 34508998468261303097519393)
      ·
        refine ⟨25881748851195977323139545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34508998468261303097519393 25881748851195977323139545)
        ·
          refine ⟨19411311638396982992354659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25881748851195977323139545 19411311638396982992354659)
          ·
            refine ⟨29116967457595474488531989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19411311638396982992354659 29116967457595474488531989)
            ·
              refine ⟨1364857849574787866649937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29116967457595474488531989 1364857849574787866649937)
              ·
                refine ⟨1023643387181090899987453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364857849574787866649937 1023643387181090899987453)
                ·
                  refine ⟨383866270192909087495295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023643387181090899987453 383866270192909087495295)
                  ·
                    rfl

theorem cell20_841024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_841024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841024 prefixEnd_841024 := by exact prefixLift 841024
  have htrace : WordTrace (prefixWord ++ tailWord_841024) baseStart_841024 baseEnd_841024 := by
    simpa [prefixWord, tailWord_841024, baseEnd_841024] using wordTrace_append hprefix tailTrace_841024
  have hstable : (prefixWord ++ tailWord_841024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841024).length < 2 ^ (prefixWord ++ tailWord_841024).sum := by decide
  have hdescent : baseEnd_841024 < baseStart_841024 := by decide
  rcases family_descends (prefixWord ++ tailWord_841024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841030 : List Nat := [6, 1, 1, 3, 1, 2, 1, 5]
def baseStart_841030 : Nat := 118140960795 + 841030 * 2 ^ 59
def prefixEnd_841030 : Nat := 4983230072969 + 3 ^ 40 * 841030 * 2
def baseEnd_841030 : Nat := 127956336252133244431757

theorem tailTrace_841030 : CollatzResearch.WordTrace tailWord_841030 prefixEnd_841030 127956336252133244431757 := by
  unfold tailWord_841030
  simp only [CollatzResearch.WordTrace]
  refine ⟨958590129471856916675767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20449922762066280889083029 958590129471856916675767)
  ·
    refine ⟨1437885194207785375013651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 958590129471856916675767 1437885194207785375013651)
    ·
      refine ⟨2156827791311678062520477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437885194207785375013651 2156827791311678062520477)
      ·
        refine ⟨808810421741879273445179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2156827791311678062520477 808810421741879273445179)
        ·
          refine ⟨1213215632612818910167769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808810421741879273445179 1213215632612818910167769)
          ·
            refine ⟨909911724459614182625827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213215632612818910167769 909911724459614182625827)
            ·
              refine ⟨1364867586689421273938741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909911724459614182625827 1364867586689421273938741)
              ·
                refine ⟨127956336252133244431757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1364867586689421273938741 127956336252133244431757)
                ·
                  rfl

theorem cell20_841030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_841030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841030 prefixEnd_841030 := by exact prefixLift 841030
  have htrace : WordTrace (prefixWord ++ tailWord_841030) baseStart_841030 baseEnd_841030 := by
    simpa [prefixWord, tailWord_841030, baseEnd_841030] using wordTrace_append hprefix tailTrace_841030
  have hstable : (prefixWord ++ tailWord_841030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841030).length < 2 ^ (prefixWord ++ tailWord_841030).sum := by decide
  have hdescent : baseEnd_841030 < baseStart_841030 := by decide
  rcases family_descends (prefixWord ++ tailWord_841030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841083 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_841083 : Nat := 118140960795 + 841083 * 2 ^ 59
def prefixEnd_841083 : Nat := 4983230072969 + 3 ^ 40 * 841083 * 2
def baseEnd_841083 : Nat := 383893199400567104528387

theorem tailTrace_841083 : CollatzResearch.WordTrace tailWord_841083 prefixEnd_841083 383893199400567104528387 := by
  unfold tailWord_841083
  simp only [CollatzResearch.WordTrace]
  refine ⟨30676817211907411385303903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20451211474604940923535935 30676817211907411385303903)
  ·
    refine ⟨46015225817861117077955855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30676817211907411385303903 46015225817861117077955855)
    ·
      refine ⟨69022838726791675616933783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46015225817861117077955855 69022838726791675616933783)
      ·
        refine ⟨103534258090187513425400675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69022838726791675616933783 103534258090187513425400675)
        ·
          refine ⟨155301387135281270138101013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103534258090187513425400675 155301387135281270138101013)
          ·
            refine ⟨7279752521966309537723485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155301387135281270138101013 7279752521966309537723485)
            ·
              refine ⟨2729907195737366076646307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7279752521966309537723485 2729907195737366076646307)
              ·
                refine ⟨4094860793606049114969461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2729907195737366076646307 4094860793606049114969461)
                ·
                  refine ⟨383893199400567104528387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4094860793606049114969461 383893199400567104528387)
                  ·
                    rfl

theorem cell20_841083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_841083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841083 prefixEnd_841083 := by exact prefixLift 841083
  have htrace : WordTrace (prefixWord ++ tailWord_841083) baseStart_841083 baseEnd_841083 := by
    simpa [prefixWord, tailWord_841083, baseEnd_841083] using wordTrace_append hprefix tailTrace_841083
  have hstable : (prefixWord ++ tailWord_841083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841083).length < 2 ^ (prefixWord ++ tailWord_841083).sum := by decide
  have hdescent : baseEnd_841083 < baseStart_841083 := by decide
  rcases family_descends (prefixWord ++ tailWord_841083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841106 : List Nat := [3, 2, 3, 3, 2, 1, 2, 4]
def baseStart_841106 : Nat := 118140960795 + 841106 * 2 ^ 59
def prefixEnd_841106 : Nat := 4983230072969 + 3 ^ 40 * 841106 * 2
def baseEnd_841106 : Nat := 127967899075760415587209

theorem tailTrace_841106 : CollatzResearch.WordTrace tailWord_841106 prefixEnd_841106 127967899075760415587209 := by
  unfold tailWord_841106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7669414022706021578347793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20451770727216057542260781 7669414022706021578347793)
  ·
    refine ⟨5752060517029516183760845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7669414022706021578347793 5752060517029516183760845)
    ·
      refine ⟨2157022693886068568910317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5752060517029516183760845 2157022693886068568910317)
      ·
        refine ⟨808883510207275713341369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2157022693886068568910317 808883510207275713341369)
        ·
          refine ⟨606662632655456785006027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808883510207275713341369 606662632655456785006027)
          ·
            refine ⟨909993948983185177509041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606662632655456785006027 909993948983185177509041)
            ·
              refine ⟨682495461737388883131781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909993948983185177509041 682495461737388883131781)
              ·
                refine ⟨127967899075760415587209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 682495461737388883131781 127967899075760415587209)
                ·
                  rfl

theorem cell20_841106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_841106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841106 prefixEnd_841106 := by exact prefixLift 841106
  have htrace : WordTrace (prefixWord ++ tailWord_841106) baseStart_841106 baseEnd_841106 := by
    simpa [prefixWord, tailWord_841106, baseEnd_841106] using wordTrace_append hprefix tailTrace_841106
  have hstable : (prefixWord ++ tailWord_841106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841106).length < 2 ^ (prefixWord ++ tailWord_841106).sum := by decide
  have hdescent : baseEnd_841106 < baseStart_841106 := by decide
  rcases family_descends (prefixWord ++ tailWord_841106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841114 : List Nat := [3, 1, 1, 4, 1, 1, 3, 6]
def baseStart_841114 : Nat := 118140960795 + 841114 * 2 ^ 59
def prefixEnd_841114 : Nat := 4983230072969 + 3 ^ 40 * 841114 * 2
def baseEnd_841114 : Nat := 127969116215089591498309

theorem tailTrace_841114 : CollatzResearch.WordTrace tailWord_841114 prefixEnd_841114 127969116215089591498309 := by
  unfold tailWord_841114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7669486968698775919920599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20451965249863402453121597 7669486968698775919920599)
  ·
    refine ⟨11504230453048163879880899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7669486968698775919920599 11504230453048163879880899)
    ·
      refine ⟨17256345679572245819821349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11504230453048163879880899 17256345679572245819821349)
      ·
        refine ⟨3235564814919796091216503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17256345679572245819821349 3235564814919796091216503)
        ·
          refine ⟨4853347222379694136824755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235564814919796091216503 4853347222379694136824755)
          ·
            refine ⟨7280020833569541205237133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853347222379694136824755 7280020833569541205237133)
            ·
              refine ⟨2730007812588577951963925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7280020833569541205237133 2730007812588577951963925)
              ·
                refine ⟨127969116215089591498309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2730007812588577951963925 127969116215089591498309)
                ·
                  rfl

theorem cell20_841114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_841114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841114 prefixEnd_841114 := by exact prefixLift 841114
  have htrace : WordTrace (prefixWord ++ tailWord_841114) baseStart_841114 baseEnd_841114 := by
    simpa [prefixWord, tailWord_841114, baseEnd_841114] using wordTrace_append hprefix tailTrace_841114
  have hstable : (prefixWord ++ tailWord_841114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841114).length < 2 ^ (prefixWord ++ tailWord_841114).sum := by decide
  have hdescent : baseEnd_841114 < baseStart_841114 := by decide
  rcases family_descends (prefixWord ++ tailWord_841114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841200 : List Nat := [2, 1, 1, 1, 3, 5, 1, 4, 2]
def baseStart_841200 : Nat := 118140960795 + 841200 * 2 ^ 59
def prefixEnd_841200 : Nat := 4983230072969 + 3 ^ 40 * 841200 * 2
def baseEnd_841200 : Nat := 383946601388634697627909

theorem tailTrace_841200 : CollatzResearch.WordTrace tailWord_841200 prefixEnd_841200 383946601388634697627909 := by
  unfold tailWord_841200
  simp only [CollatzResearch.WordTrace]
  refine ⟨15340542276241770183656527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20454056368322360244875369 15340542276241770183656527)
  ·
    refine ⟨23010813414362655275484791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15340542276241770183656527 23010813414362655275484791)
    ·
      refine ⟨34516220121543982913227187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23010813414362655275484791 34516220121543982913227187)
      ·
        refine ⟨51774330182315974369840781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34516220121543982913227187 51774330182315974369840781)
        ·
          refine ⟨19415373818368490388690293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51774330182315974369840781 19415373818368490388690293)
          ·
            refine ⟨1820191295472045973939715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19415373818368490388690293 1820191295472045973939715)
            ·
              refine ⟨2730286943208068960909573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820191295472045973939715 2730286943208068960909573)
              ·
                refine ⟨511928801851512930170545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2730286943208068960909573 511928801851512930170545)
                ·
                  refine ⟨383946601388634697627909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511928801851512930170545 383946601388634697627909)
                  ·
                    rfl

theorem cell20_841200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_841200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841200 prefixEnd_841200 := by exact prefixLift 841200
  have htrace : WordTrace (prefixWord ++ tailWord_841200) baseStart_841200 baseEnd_841200 := by
    simpa [prefixWord, tailWord_841200, baseEnd_841200] using wordTrace_append hprefix tailTrace_841200
  have hstable : (prefixWord ++ tailWord_841200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841200).length < 2 ^ (prefixWord ++ tailWord_841200).sum := by decide
  have hdescent : baseEnd_841200 < baseStart_841200 := by decide
  rcases family_descends (prefixWord ++ tailWord_841200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841242 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_841242 : Nat := 118140960795 + 841242 * 2 ^ 59
def prefixEnd_841242 : Nat := 4983230072969 + 3 ^ 40 * 841242 * 2
def baseEnd_841242 : Nat := 383965771333069218227737

theorem tailTrace_841242 : CollatzResearch.WordTrace tailWord_841242 prefixEnd_841242 383965771333069218227737 := by
  unfold tailWord_841242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670654104582845385085495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20455077612220921026894653 7670654104582845385085495)
  ·
    refine ⟨11505981156874268077628243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7670654104582845385085495 11505981156874268077628243)
    ·
      refine ⟨17258971735311402116442365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11505981156874268077628243 17258971735311402116442365)
      ·
        refine ⟨6472114400741775793665887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17258971735311402116442365 6472114400741775793665887)
        ·
          refine ⟨9708171601112663690498831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472114400741775793665887 9708171601112663690498831)
          ·
            refine ⟨14562257401668995535748247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9708171601112663690498831 14562257401668995535748247)
            ·
              refine ⟨21843386102503493303622371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14562257401668995535748247 21843386102503493303622371)
              ·
                refine ⟨32765079153755239955433557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21843386102503493303622371 32765079153755239955433557)
                ·
                  refine ⟨383965771333069218227737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32765079153755239955433557 383965771333069218227737)
                  ·
                    rfl

theorem cell20_841242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_841242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841242 prefixEnd_841242 := by exact prefixLift 841242
  have htrace : WordTrace (prefixWord ++ tailWord_841242) baseStart_841242 baseEnd_841242 := by
    simpa [prefixWord, tailWord_841242, baseEnd_841242] using wordTrace_append hprefix tailTrace_841242
  have hstable : (prefixWord ++ tailWord_841242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841242).length < 2 ^ (prefixWord ++ tailWord_841242).sum := by decide
  have hdescent : baseEnd_841242 < baseStart_841242 := by decide
  rcases family_descends (prefixWord ++ tailWord_841242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841269 : List Nat := [1, 3, 3, 1, 1, 4, 3, 1, 3]
def baseStart_841269 : Nat := 118140960795 + 841269 * 2 ^ 59
def prefixEnd_841269 : Nat := 4983230072969 + 3 ^ 40 * 841269 * 2
def baseEnd_841269 : Nat := 383978094868777124327627

theorem tailTrace_841269 : CollatzResearch.WordTrace tailWord_841269 prefixEnd_841269 383978094868777124327627 := by
  unfold tailWord_841269
  simp only [CollatzResearch.WordTrace]
  refine ⟨30683601189233565151574861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20455734126155710101049907 30683601189233565151574861)
  ·
    refine ⟨11506350445962586931840573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30683601189233565151574861 11506350445962586931840573)
    ·
      refine ⟨4314881417235970099440215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11506350445962586931840573 4314881417235970099440215)
      ·
        refine ⟨6472322125853955149160323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314881417235970099440215 6472322125853955149160323)
        ·
          refine ⟨9708483188780932723740485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472322125853955149160323 9708483188780932723740485)
          ·
            refine ⟨1820340597896424885701341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9708483188780932723740485 1820340597896424885701341)
            ·
              refine ⟨682627724211159332138003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1820340597896424885701341 682627724211159332138003)
              ·
                refine ⟨1023941586316738998207005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682627724211159332138003 1023941586316738998207005)
                ·
                  refine ⟨383978094868777124327627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023941586316738998207005 383978094868777124327627)
                  ·
                    rfl

theorem cell20_841269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_841269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841269 prefixEnd_841269 := by exact prefixLift 841269
  have htrace : WordTrace (prefixWord ++ tailWord_841269) baseStart_841269 baseEnd_841269 := by
    simpa [prefixWord, tailWord_841269, baseEnd_841269] using wordTrace_append hprefix tailTrace_841269
  have hstable : (prefixWord ++ tailWord_841269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841269).length < 2 ^ (prefixWord ++ tailWord_841269).sum := by decide
  have hdescent : baseEnd_841269 < baseStart_841269 := by decide
  rcases family_descends (prefixWord ++ tailWord_841269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841328 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 3]
def baseStart_841328 : Nat := 118140960795 + 841328 * 2 ^ 59
def prefixEnd_841328 : Nat := 4983230072969 + 3 ^ 40 * 841328 * 2
def baseEnd_841328 : Nat := 384005024076435141360719

theorem tailTrace_841328 : CollatzResearch.WordTrace tailWord_841328 prefixEnd_841328 384005024076435141360719 := by
  unfold tailWord_841328
  simp only [CollatzResearch.WordTrace]
  refine ⟨15342876548009909113986319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20457168730679878818648425 15342876548009909113986319)
  ·
    refine ⟨23014314822014863670979479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15342876548009909113986319 23014314822014863670979479)
    ·
      refine ⟨34521472233022295506469219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23014314822014863670979479 34521472233022295506469219)
      ·
        refine ⟨51782208349533443259703829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34521472233022295506469219 51782208349533443259703829)
        ·
          refine ⟨2427291016384380152798617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51782208349533443259703829 2427291016384380152798617)
          ·
            refine ⟨1820468262288285114598963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2427291016384380152798617 1820468262288285114598963)
            ·
              refine ⟨2730702393432427671898445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820468262288285114598963 2730702393432427671898445)
              ·
                refine ⟨1024013397537160376961917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2730702393432427671898445 1024013397537160376961917)
                ·
                  refine ⟨384005024076435141360719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024013397537160376961917 384005024076435141360719)
                  ·
                    rfl

theorem cell20_841328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_841328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841328 prefixEnd_841328 := by exact prefixLift 841328
  have htrace : WordTrace (prefixWord ++ tailWord_841328) baseStart_841328 baseEnd_841328 := by
    simpa [prefixWord, tailWord_841328, baseEnd_841328] using wordTrace_append hprefix tailTrace_841328
  have hstable : (prefixWord ++ tailWord_841328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841328).length < 2 ^ (prefixWord ++ tailWord_841328).sum := by decide
  have hdescent : baseEnd_841328 < baseStart_841328 := by decide
  rcases family_descends (prefixWord ++ tailWord_841328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841380 : List Nat := [2, 3, 1, 2, 2, 2, 3, 5]
def baseStart_841380 : Nat := 118140960795 + 841380 * 2 ^ 59
def prefixEnd_841380 : Nat := 4983230072969 + 3 ^ 40 * 841380 * 2
def baseEnd_841380 : Nat := 128009586097784690542391

theorem tailTrace_841380 : CollatzResearch.WordTrace tailWord_841380 prefixEnd_841380 128009586097784690542391 := by
  unfold tailWord_841380
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343824845915715554432797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20458433127887620739243729 15343824845915715554432797)
  ·
    refine ⟨5753934317218393332912299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15343824845915715554432797 5753934317218393332912299)
    ·
      refine ⟨8630901475827589999368449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5753934317218393332912299 8630901475827589999368449)
      ·
        refine ⟨6473176106870692499526337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8630901475827589999368449 6473176106870692499526337)
        ·
          refine ⟨4854882080153019374644753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6473176106870692499526337 4854882080153019374644753)
          ·
            refine ⟨3641161560114764530983565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4854882080153019374644753 3641161560114764530983565)
            ·
              refine ⟨1365435585043036699118837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3641161560114764530983565 1365435585043036699118837)
              ·
                refine ⟨128009586097784690542391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1365435585043036699118837 128009586097784690542391)
                ·
                  rfl

theorem cell20_841380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_841380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841380 prefixEnd_841380 := by exact prefixLift 841380
  have htrace : WordTrace (prefixWord ++ tailWord_841380) baseStart_841380 baseEnd_841380 := by
    simpa [prefixWord, tailWord_841380, baseEnd_841380] using wordTrace_append hprefix tailTrace_841380
  have hstable : (prefixWord ++ tailWord_841380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841380).length < 2 ^ (prefixWord ++ tailWord_841380).sum := by decide
  have hdescent : baseEnd_841380 < baseStart_841380 := by decide
  rcases family_descends (prefixWord ++ tailWord_841380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841394 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_841394 : Nat := 118140960795 + 841394 * 2 ^ 59
def prefixEnd_841394 : Nat := 4983230072969 + 3 ^ 40 * 841394 * 2
def baseEnd_841394 : Nat := 384035148274832245160449

theorem tailTrace_841394 : CollatzResearch.WordTrace tailWord_841394 prefixEnd_841394 384035148274832245160449 := by
  unfold tailWord_841394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7672040078445177874968809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20458773542520474333250157 7672040078445177874968809)
  ·
    refine ⟨5754030058833883406226607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7672040078445177874968809 5754030058833883406226607)
    ·
      refine ⟨8631045088250825109339911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5754030058833883406226607 8631045088250825109339911)
      ·
        refine ⟨12946567632376237664009867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631045088250825109339911 12946567632376237664009867)
        ·
          refine ⟨19419851448564356496014801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12946567632376237664009867 19419851448564356496014801)
          ·
            refine ⟨14564888586423267372011101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19419851448564356496014801 14564888586423267372011101)
            ·
              refine ⟨5461833219908725264504163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14564888586423267372011101 5461833219908725264504163)
              ·
                refine ⟨8192749829863087896756245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461833219908725264504163 8192749829863087896756245)
                ·
                  refine ⟨384035148274832245160449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8192749829863087896756245 384035148274832245160449)
                  ·
                    rfl

theorem cell20_841394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_841394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841394 prefixEnd_841394 := by exact prefixLift 841394
  have htrace : WordTrace (prefixWord ++ tailWord_841394) baseStart_841394 baseEnd_841394 := by
    simpa [prefixWord, tailWord_841394, baseEnd_841394] using wordTrace_append hprefix tailTrace_841394
  have hstable : (prefixWord ++ tailWord_841394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841394).length < 2 ^ (prefixWord ++ tailWord_841394).sum := by decide
  have hdescent : baseEnd_841394 < baseStart_841394 := by decide
  rcases family_descends (prefixWord ++ tailWord_841394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841401 : List Nat := [1, 2, 1, 4, 1, 1, 2, 8]
def baseStart_841401 : Nat := 118140960795 + 841401 * 2 ^ 59
def prefixEnd_841401 : Nat := 4983230072969 + 3 ^ 40 * 841401 * 2
def baseEnd_841401 : Nat := 128012781088523777309029

theorem tailTrace_841401 : CollatzResearch.WordTrace tailWord_841401 prefixEnd_841401 128012781088523777309029 := by
  unfold tailWord_841401
  simp only [CollatzResearch.WordTrace]
  refine ⟨30688415624755351695380057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20458943749836901130253371 30688415624755351695380057)
  ·
    refine ⟨23016311718566513771535043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30688415624755351695380057 23016311718566513771535043)
    ·
      refine ⟨34524467577849770657302565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23016311718566513771535043 34524467577849770657302565)
      ·
        refine ⟨6473337670846831998244231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34524467577849770657302565 6473337670846831998244231)
        ·
          refine ⟨9710006506270247997366347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473337670846831998244231 9710006506270247997366347)
          ·
            refine ⟨14565009759405371996049521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9710006506270247997366347 14565009759405371996049521)
            ·
              refine ⟨10923757319554028997037141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14565009759405371996049521 10923757319554028997037141)
              ·
                refine ⟨128012781088523777309029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10923757319554028997037141 128012781088523777309029)
                ·
                  rfl

theorem cell20_841401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_841401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841401 prefixEnd_841401 := by exact prefixLift 841401
  have htrace : WordTrace (prefixWord ++ tailWord_841401) baseStart_841401 baseEnd_841401 := by
    simpa [prefixWord, tailWord_841401, baseEnd_841401] using wordTrace_append hprefix tailTrace_841401
  have hstable : (prefixWord ++ tailWord_841401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841401).length < 2 ^ (prefixWord ++ tailWord_841401).sum := by decide
  have hdescent : baseEnd_841401 < baseStart_841401 := by decide
  rcases family_descends (prefixWord ++ tailWord_841401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841414 : List Nat := [6, 1, 2, 1, 1, 2, 7]
def baseStart_841414 : Nat := 118140960795 + 841414 * 2 ^ 59
def prefixEnd_841414 : Nat := 4983230072969 + 3 ^ 40 * 841414 * 2
def baseEnd_841414 : Nat := 42671586313311229388189

theorem tailTrace_841414 : CollatzResearch.WordTrace tailWord_841414 prefixEnd_841414 42671586313311229388189 := by
  unfold tailWord_841414
  simp only [CollatzResearch.WordTrace]
  refine ⟨959027805428382966112603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20459259849138836610402197 959027805428382966112603)
  ·
    refine ⟨1438541708142574449168905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 959027805428382966112603 1438541708142574449168905)
    ·
      refine ⟨1078906281106930836876679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1438541708142574449168905 1078906281106930836876679)
      ·
        refine ⟨1618359421660396255315019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078906281106930836876679 1618359421660396255315019)
        ·
          refine ⟨2427539132490594382972529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618359421660396255315019 2427539132490594382972529)
          ·
            refine ⟨1820654349367945787229397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2427539132490594382972529 1820654349367945787229397)
            ·
              refine ⟨42671586313311229388189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1820654349367945787229397 42671586313311229388189)
              ·
                rfl

theorem cell20_841414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 7].length) (baseStart_841414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841414 prefixEnd_841414 := by exact prefixLift 841414
  have htrace : WordTrace (prefixWord ++ tailWord_841414) baseStart_841414 baseEnd_841414 := by
    simpa [prefixWord, tailWord_841414, baseEnd_841414] using wordTrace_append hprefix tailTrace_841414
  have hstable : (prefixWord ++ tailWord_841414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841414).length < 2 ^ (prefixWord ++ tailWord_841414).sum := by decide
  have hdescent : baseEnd_841414 < baseStart_841414 := by decide
  rcases family_descends (prefixWord ++ tailWord_841414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841418 : List Nat := [3, 1, 2, 1, 5, 1, 7]
def baseStart_841418 : Nat := 118140960795 + 841418 * 2 ^ 59
def prefixEnd_841418 : Nat := 4983230072969 + 3 ^ 40 * 841418 * 2
def baseEnd_841418 : Nat := 42671789169866092040039

theorem tailTrace_841418 : CollatzResearch.WordTrace tailWord_841418 prefixEnd_841418 42671789169866092040039 := by
  unfold tailWord_841418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7672258916423440899687227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20459357110462509065832605 7672258916423440899687227)
  ·
    refine ⟨11508388374635161349530841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7672258916423440899687227 11508388374635161349530841)
    ·
      refine ⟨8631291280976371012148131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11508388374635161349530841 8631291280976371012148131)
      ·
        refine ⟨12946936921464556518222197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631291280976371012148131 12946936921464556518222197)
        ·
          refine ⟨1213775336387302173583331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12946936921464556518222197 1213775336387302173583331)
          ·
            refine ⟨1820663004580953260374997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213775336387302173583331 1820663004580953260374997)
            ·
              refine ⟨42671789169866092040039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1820663004580953260374997 42671789169866092040039)
              ·
                rfl

theorem cell20_841418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 7].length) (baseStart_841418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841418 prefixEnd_841418 := by exact prefixLift 841418
  have htrace : WordTrace (prefixWord ++ tailWord_841418) baseStart_841418 baseEnd_841418 := by
    simpa [prefixWord, tailWord_841418, baseEnd_841418] using wordTrace_append hprefix tailTrace_841418
  have hstable : (prefixWord ++ tailWord_841418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841418).length < 2 ^ (prefixWord ++ tailWord_841418).sum := by decide
  have hdescent : baseEnd_841418 < baseStart_841418 := by decide
  rcases family_descends (prefixWord ++ tailWord_841418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841421 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 5]
def baseStart_841421 : Nat := 118140960795 + 841421 * 2 ^ 59
def prefixEnd_841421 : Nat := 4983230072969 + 3 ^ 40 * 841421 * 2
def baseEnd_841421 : Nat := 384047471810540151260339

theorem tailTrace_841421 : CollatzResearch.WordTrace tailWord_841421 prefixEnd_841421 384047471810540151260339 := by
  unfold tailWord_841421
  simp only [CollatzResearch.WordTrace]
  refine ⟨30689145084682895111108117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20459430056455263407405411 30689145084682895111108117)
  ·
    refine ⟨1438553675844510708333193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30689145084682895111108117 1438553675844510708333193)
    ·
      refine ⟨1078915256883383031249895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1438553675844510708333193 1078915256883383031249895)
      ·
        refine ⟨1618372885325074546874843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078915256883383031249895 1618372885325074546874843)
        ·
          refine ⟨2427559327987611820312265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618372885325074546874843 2427559327987611820312265)
          ·
            refine ⟨1820669495990708865234199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2427559327987611820312265 1820669495990708865234199)
            ·
              refine ⟨2731004243986063297851299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820669495990708865234199 2731004243986063297851299)
              ·
                refine ⟨4096506365979094946776949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731004243986063297851299 4096506365979094946776949)
                ·
                  refine ⟨384047471810540151260339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4096506365979094946776949 384047471810540151260339)
                  ·
                    rfl

theorem cell20_841421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_841421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841421 prefixEnd_841421 := by exact prefixLift 841421
  have htrace : WordTrace (prefixWord ++ tailWord_841421) baseStart_841421 baseEnd_841421 := by
    simpa [prefixWord, tailWord_841421, baseEnd_841421] using wordTrace_append hprefix tailTrace_841421
  have hstable : (prefixWord ++ tailWord_841421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841421).length < 2 ^ (prefixWord ++ tailWord_841421).sum := by decide
  have hdescent : baseEnd_841421 < baseStart_841421 := by decide
  rcases family_descends (prefixWord ++ tailWord_841421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841425 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_841425 : Nat := 118140960795 + 841425 * 2 ^ 59
def prefixEnd_841425 : Nat := 4983230072969 + 3 ^ 40 * 841425 * 2
def baseEnd_841425 : Nat := 384049297519533915126989

theorem tailTrace_841425 : CollatzResearch.WordTrace tailWord_841425 prefixEnd_841425 384049297519533915126989 := by
  unfold tailWord_841425
  simp only [CollatzResearch.WordTrace]
  refine ⟨30689290976668403794253729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20459527317778935862835819 30689290976668403794253729)
  ·
    refine ⟨23016968232501302845690297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30689290976668403794253729 23016968232501302845690297)
    ·
      refine ⟨17262726174375977134267723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23016968232501302845690297 17262726174375977134267723)
      ·
        refine ⟨25894089261563965701401585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17262726174375977134267723 25894089261563965701401585)
        ·
          refine ⟨19420566946172974276051189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25894089261563965701401585 19420566946172974276051189)
          ·
            refine ⟨1820678151203716338379799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19420566946172974276051189 1820678151203716338379799)
            ·
              refine ⟨2731017226805574507569699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820678151203716338379799 2731017226805574507569699)
              ·
                refine ⟨4096525840208361761354549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731017226805574507569699 4096525840208361761354549)
                ·
                  refine ⟨384049297519533915126989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4096525840208361761354549 384049297519533915126989)
                  ·
                    rfl

theorem cell20_841425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_841425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841425 prefixEnd_841425 := by exact prefixLift 841425
  have htrace : WordTrace (prefixWord ++ tailWord_841425) baseStart_841425 baseEnd_841425 := by
    simpa [prefixWord, tailWord_841425, baseEnd_841425] using wordTrace_append hprefix tailTrace_841425
  have hstable : (prefixWord ++ tailWord_841425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841425).length < 2 ^ (prefixWord ++ tailWord_841425).sum := by decide
  have hdescent : baseEnd_841425 < baseStart_841425 := by decide
  rcases family_descends (prefixWord ++ tailWord_841425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841428 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_841428 : Nat := 118140960795 + 841428 * 2 ^ 59
def prefixEnd_841428 : Nat := 4983230072969 + 3 ^ 40 * 841428 * 2
def baseEnd_841428 : Nat := 384050666801279238026977

theorem tailTrace_841428 : CollatzResearch.WordTrace tailWord_841428 prefixEnd_841428 384050666801279238026977 := by
  unfold tailWord_841428
  simp only [CollatzResearch.WordTrace]
  refine ⟨15344700197828767653306469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20459600263771690204408625 15344700197828767653306469)
  ·
    refine ⟨2877131287092893934994963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15344700197828767653306469 2877131287092893934994963)
    ·
      refine ⟨4315696930639340902492445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877131287092893934994963 4315696930639340902492445)
      ·
        refine ⟨1618386348989752838434667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4315696930639340902492445 1618386348989752838434667)
        ·
          refine ⟨2427579523484629257652001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618386348989752838434667 2427579523484629257652001)
          ·
            refine ⟨1820684642613471943239001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2427579523484629257652001 1820684642613471943239001)
            ·
              refine ⟨1365513481960103957429251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1820684642613471943239001 1365513481960103957429251)
              ·
                refine ⟨2048270222940155936143877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365513481960103957429251 2048270222940155936143877)
                ·
                  refine ⟨384050666801279238026977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2048270222940155936143877 384050666801279238026977)
                  ·
                    rfl

theorem cell20_841428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_841428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841428 prefixEnd_841428 := by exact prefixLift 841428
  have htrace : WordTrace (prefixWord ++ tailWord_841428) baseStart_841428 baseEnd_841428 := by
    simpa [prefixWord, tailWord_841428, baseEnd_841428] using wordTrace_append hprefix tailTrace_841428
  have hstable : (prefixWord ++ tailWord_841428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841428).length < 2 ^ (prefixWord ++ tailWord_841428).sum := by decide
  have hdescent : baseEnd_841428 < baseStart_841428 := by decide
  rcases family_descends (prefixWord ++ tailWord_841428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841439 : List Nat := [1, 1, 2, 3, 2, 2, 2, 7]
def baseStart_841439 : Nat := 118140960795 + 841439 * 2 ^ 59
def prefixEnd_841439 : Nat := 4983230072969 + 3 ^ 40 * 841439 * 2
def baseEnd_841439 : Nat := 128018562500337362886755

theorem tailTrace_841439 : CollatzResearch.WordTrace tailWord_841439 prefixEnd_841439 128018562500337362886755 := by
  unfold tailWord_841439
  simp only [CollatzResearch.WordTrace]
  refine ⟨30689801598617684185263371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20459867732411789456842247 30689801598617684185263371)
  ·
    refine ⟨46034702397926526277895057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30689801598617684185263371 46034702397926526277895057)
    ·
      refine ⟨34526026798444894708421293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46034702397926526277895057 34526026798444894708421293)
      ·
        refine ⟨12947260049416835515657985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34526026798444894708421293 12947260049416835515657985)
        ·
          refine ⟨9710445037062626636743489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12947260049416835515657985 9710445037062626636743489)
          ·
            refine ⟨7282833777796969977557617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9710445037062626636743489 7282833777796969977557617)
            ·
              refine ⟨5462125333347727483168213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7282833777796969977557617 5462125333347727483168213)
              ·
                refine ⟨128018562500337362886755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5462125333347727483168213 128018562500337362886755)
                ·
                  rfl

theorem cell20_841439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_841439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841439 prefixEnd_841439 := by exact prefixLift 841439
  have htrace : WordTrace (prefixWord ++ tailWord_841439) baseStart_841439 baseEnd_841439 := by
    simpa [prefixWord, tailWord_841439, baseEnd_841439] using wordTrace_append hprefix tailTrace_841439
  have hstable : (prefixWord ++ tailWord_841439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841439).length < 2 ^ (prefixWord ++ tailWord_841439).sum := by decide
  have hdescent : baseEnd_841439 < baseStart_841439 := by decide
  rcases family_descends (prefixWord ++ tailWord_841439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841539 : List Nat := [1, 1, 1, 3, 1, 5, 1, 4, 3]
def baseStart_841539 : Nat := 118140960795 + 841539 * 2 ^ 59
def prefixEnd_841539 : Nat := 4983230072969 + 3 ^ 40 * 841539 * 2
def baseEnd_841539 : Nat := 384101330225856185326523

theorem tailTrace_841539 : CollatzResearch.WordTrace tailWord_841539 prefixEnd_841539 384101330225856185326523 := by
  unfold tailWord_841539
  simp only [CollatzResearch.WordTrace]
  refine ⟨30693448898255401263903671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20462299265503600842602447 30693448898255401263903671)
  ·
    refine ⟨46040173347383101895855507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30693448898255401263903671 46040173347383101895855507)
    ·
      refine ⟨69060260021074652843783261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46040173347383101895855507 69060260021074652843783261)
      ·
        refine ⟨25897597507902994816418723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69060260021074652843783261 25897597507902994816418723)
        ·
          refine ⟨38846396261854492224628085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25897597507902994816418723 38846396261854492224628085)
          ·
            refine ⟨3641849649548858646058883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38846396261854492224628085 3641849649548858646058883)
            ·
              refine ⟨5462774474323287969088325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641849649548858646058883 5462774474323287969088325)
              ·
                refine ⟨1024270213935616494204061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5462774474323287969088325 1024270213935616494204061)
                ·
                  refine ⟨384101330225856185326523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024270213935616494204061 384101330225856185326523)
                  ·
                    rfl

theorem cell20_841539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 3].length) (baseStart_841539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841539 prefixEnd_841539 := by exact prefixLift 841539
  have htrace : WordTrace (prefixWord ++ tailWord_841539) baseStart_841539 baseEnd_841539 := by
    simpa [prefixWord, tailWord_841539, baseEnd_841539] using wordTrace_append hprefix tailTrace_841539
  have hstable : (prefixWord ++ tailWord_841539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841539).length < 2 ^ (prefixWord ++ tailWord_841539).sum := by decide
  have hdescent : baseEnd_841539 < baseStart_841539 := by decide
  rcases family_descends (prefixWord ++ tailWord_841539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841546 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_841546 : Nat := 118140960795 + 841546 * 2 ^ 59
def prefixEnd_841546 : Nat := 4983230072969 + 3 ^ 40 * 841546 * 2
def baseEnd_841546 : Nat := 384104525216595272093161

theorem tailTrace_841546 : CollatzResearch.WordTrace tailWord_841546 prefixEnd_841546 384104525216595272093161 := by
  unfold tailWord_841546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7673426052307510364852123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20462469472820027639605661 7673426052307510364852123)
  ·
    refine ⟨11510139078461265547278185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7673426052307510364852123 11510139078461265547278185)
    ·
      refine ⟨8632604308845949160458639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11510139078461265547278185 8632604308845949160458639)
      ·
        refine ⟨12948906463268923740687959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8632604308845949160458639 12948906463268923740687959)
        ·
          refine ⟨19423359694903385611031939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12948906463268923740687959 19423359694903385611031939)
          ·
            refine ⟨29135039542355078416547909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19423359694903385611031939 29135039542355078416547909)
            ·
              refine ⟨5462819914191577203102733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29135039542355078416547909 5462819914191577203102733)
              ·
                refine ⟨2048557467821841451163525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5462819914191577203102733 2048557467821841451163525)
                ·
                  refine ⟨384104525216595272093161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2048557467821841451163525 384104525216595272093161)
                  ·
                    rfl

theorem cell20_841546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_841546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841546 prefixEnd_841546 := by exact prefixLift 841546
  have htrace : WordTrace (prefixWord ++ tailWord_841546) baseStart_841546 baseEnd_841546 := by
    simpa [prefixWord, tailWord_841546, baseEnd_841546] using wordTrace_append hprefix tailTrace_841546
  have hstable : (prefixWord ++ tailWord_841546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841546).length < 2 ^ (prefixWord ++ tailWord_841546).sum := by decide
  have hdescent : baseEnd_841546 < baseStart_841546 := by decide
  rcases family_descends (prefixWord ++ tailWord_841546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841549 : List Nat := [1, 6, 1, 2, 1, 1, 3, 5]
def baseStart_841549 : Nat := 118140960795 + 841549 * 2 ^ 59
def prefixEnd_841549 : Nat := 4983230072969 + 3 ^ 40 * 841549 * 2
def baseEnd_841549 : Nat := 128035298166113531664383

theorem tailTrace_841549 : CollatzResearch.WordTrace tailWord_841549 prefixEnd_841549 128035298166113531664383 := by
  unfold tailWord_841549
  simp only [CollatzResearch.WordTrace]
  refine ⟨30693813628219172971767701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20462542418812781981178467 30693813628219172971767701)
  ·
    refine ⟨1438772513822773733051611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30693813628219172971767701 1438772513822773733051611)
    ·
      refine ⟨2158158770734160599577417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1438772513822773733051611 2158158770734160599577417)
      ·
        refine ⟨1618619078050620449683063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2158158770734160599577417 1618619078050620449683063)
        ·
          refine ⟨2427928617075930674524595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618619078050620449683063 2427928617075930674524595)
          ·
            refine ⟨3641892925613896011786893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427928617075930674524595 3641892925613896011786893)
            ·
              refine ⟨1365709847105211004420085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3641892925613896011786893 1365709847105211004420085)
              ·
                refine ⟨128035298166113531664383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1365709847105211004420085 128035298166113531664383)
                ·
                  rfl

theorem cell20_841549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_841549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841549 prefixEnd_841549 := by exact prefixLift 841549
  have htrace : WordTrace (prefixWord ++ tailWord_841549) baseStart_841549 baseEnd_841549 := by
    simpa [prefixWord, tailWord_841549, baseEnd_841549] using wordTrace_append hprefix tailTrace_841549
  have hstable : (prefixWord ++ tailWord_841549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841549).length < 2 ^ (prefixWord ++ tailWord_841549).sum := by decide
  have hdescent : baseEnd_841549 < baseStart_841549 := by decide
  rcases family_descends (prefixWord ++ tailWord_841549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841556 : List Nat := [2, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_841556 : Nat := 118140960795 + 841556 * 2 ^ 59
def prefixEnd_841556 : Nat := 4983230072969 + 3 ^ 40 * 841556 * 2
def baseEnd_841556 : Nat := 384109089489079681759787

theorem tailTrace_841556 : CollatzResearch.WordTrace tailWord_841556 prefixEnd_841556 384109089489079681759787 := by
  unfold tailWord_841556
  simp only [CollatzResearch.WordTrace]
  refine ⟨15347034469596906583636261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20462712626129208778181681 15347034469596906583636261)
  ·
    refine ⟨2877568963049419984431799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15347034469596906583636261 2877568963049419984431799)
    ·
      refine ⟨4316353444574129976647699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877568963049419984431799 4316353444574129976647699)
      ·
        refine ⟨6474530166861194964971549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4316353444574129976647699 6474530166861194964971549)
        ·
          refine ⟨2427948812572948111864331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6474530166861194964971549 2427948812572948111864331)
          ·
            refine ⟨3641923218859422167796497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427948812572948111864331 3641923218859422167796497)
            ·
              refine ⟨2731442414144566625847373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3641923218859422167796497 2731442414144566625847373)
              ·
                refine ⟨1024290905304212484692765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2731442414144566625847373 1024290905304212484692765)
                ·
                  refine ⟨384109089489079681759787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024290905304212484692765 384109089489079681759787)
                  ·
                    rfl

theorem cell20_841556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_841556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841556 prefixEnd_841556 := by exact prefixLift 841556
  have htrace : WordTrace (prefixWord ++ tailWord_841556) baseStart_841556 baseEnd_841556 := by
    simpa [prefixWord, tailWord_841556, baseEnd_841556] using wordTrace_append hprefix tailTrace_841556
  have hstable : (prefixWord ++ tailWord_841556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841556).length < 2 ^ (prefixWord ++ tailWord_841556).sum := by decide
  have hdescent : baseEnd_841556 < baseStart_841556 := by decide
  rcases family_descends (prefixWord ++ tailWord_841556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841560 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_841560 : Nat := 118140960795 + 841560 * 2 ^ 59
def prefixEnd_841560 : Nat := 4983230072969 + 3 ^ 40 * 841560 * 2
def baseEnd_841560 : Nat := 384110915198073445626437

theorem tailTrace_841560 : CollatzResearch.WordTrace tailWord_841560 prefixEnd_841560 384110915198073445626437 := by
  unfold tailWord_841560
  simp only [CollatzResearch.WordTrace]
  refine ⟨15347107415589660925209067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20462809887452881233612089 15347107415589660925209067)
  ·
    refine ⟨23020661123384491387813601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15347107415589660925209067 23020661123384491387813601)
    ·
      refine ⟨17265495842538368540860201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23020661123384491387813601 17265495842538368540860201)
      ·
        refine ⟨12949121881903776405645151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17265495842538368540860201 12949121881903776405645151)
        ·
          refine ⟨19423682822855664608467727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12949121881903776405645151 19423682822855664608467727)
          ·
            refine ⟨29135524234283496912701591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19423682822855664608467727 29135524234283496912701591)
            ·
              refine ⟨43703286351425245369052387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29135524234283496912701591 43703286351425245369052387)
              ·
                refine ⟨65554929527137868053578581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43703286351425245369052387 65554929527137868053578581)
                ·
                  refine ⟨384110915198073445626437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65554929527137868053578581 384110915198073445626437)
                  ·
                    rfl

theorem cell20_841560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_841560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841560 prefixEnd_841560 := by exact prefixLift 841560
  have htrace : WordTrace (prefixWord ++ tailWord_841560) baseStart_841560 baseEnd_841560 := by
    simpa [prefixWord, tailWord_841560, baseEnd_841560] using wordTrace_append hprefix tailTrace_841560
  have hstable : (prefixWord ++ tailWord_841560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841560).length < 2 ^ (prefixWord ++ tailWord_841560).sum := by decide
  have hdescent : baseEnd_841560 < baseStart_841560 := by decide
  rcases family_descends (prefixWord ++ tailWord_841560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841580 : List Nat := [2, 2, 1, 1, 4, 3, 2, 3, 2]
def baseStart_841580 : Nat := 118140960795 + 841580 * 2 ^ 59
def prefixEnd_841580 : Nat := 4983230072969 + 3 ^ 40 * 841580 * 2
def baseEnd_841580 : Nat := 384120043743042264959689

theorem tailTrace_841580 : CollatzResearch.WordTrace tailWord_841580 prefixEnd_841580 384120043743042264959689 := by
  unfold tailWord_841580
  simp only [CollatzResearch.WordTrace]
  refine ⟨15347472145553432633073097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20463296194071243510764129 15347472145553432633073097)
  ·
    refine ⟨11510604109165074474804823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15347472145553432633073097 11510604109165074474804823)
    ·
      refine ⟨17265906163747611712207235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11510604109165074474804823 17265906163747611712207235)
      ·
        refine ⟨25898859245621417568310853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17265906163747611712207235 25898859245621417568310853)
        ·
          refine ⟨4856036108554015794058285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25898859245621417568310853 4856036108554015794058285)
          ·
            refine ⟨1821013540707755922771857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4856036108554015794058285 1821013540707755922771857)
            ·
              refine ⟨1365760155530816942078893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1821013540707755922771857 1365760155530816942078893)
              ·
                refine ⟨512160058324056353279585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1365760155530816942078893 512160058324056353279585)
                ·
                  refine ⟨384120043743042264959689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512160058324056353279585 384120043743042264959689)
                  ·
                    rfl

theorem cell20_841580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_841580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841580 prefixEnd_841580 := by exact prefixLift 841580
  have htrace : WordTrace (prefixWord ++ tailWord_841580) baseStart_841580 baseEnd_841580 := by
    simpa [prefixWord, tailWord_841580, baseEnd_841580] using wordTrace_append hprefix tailTrace_841580
  have hstable : (prefixWord ++ tailWord_841580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841580).length < 2 ^ (prefixWord ++ tailWord_841580).sum := by decide
  have hdescent : baseEnd_841580 < baseStart_841580 := by decide
  rcases family_descends (prefixWord ++ tailWord_841580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841590 : List Nat := [5, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_841590 : Nat := 118140960795 + 841590 * 2 ^ 59
def prefixEnd_841590 : Nat := 4983230072969 + 3 ^ 40 * 841590 * 2
def baseEnd_841590 : Nat := 384124608015526674626315

theorem tailTrace_841590 : CollatzResearch.WordTrace tailWord_841590 prefixEnd_841590 384124608015526674626315 := by
  unfold tailWord_841590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918456813816914810875639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20463539347380424649340149 1918456813816914810875639)
  ·
    refine ⟨2877685220725372216313459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1918456813816914810875639 2877685220725372216313459)
    ·
      refine ⟨4316527831088058324470189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877685220725372216313459 4316527831088058324470189)
      ·
        refine ⟨1618697936658021871676321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4316527831088058324470189 1618697936658021871676321)
        ·
          refine ⟨1214023452493516403757241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1618697936658021871676321 1214023452493516403757241)
          ·
            refine ⟨910517589370137302817931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1214023452493516403757241 910517589370137302817931)
            ·
              refine ⟨1365776384055205954226897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910517589370137302817931 1365776384055205954226897)
              ·
                refine ⟨1024332288041404465670173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1365776384055205954226897 1024332288041404465670173)
                ·
                  refine ⟨384124608015526674626315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024332288041404465670173 384124608015526674626315)
                  ·
                    rfl

theorem cell20_841590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_841590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841590 prefixEnd_841590 := by exact prefixLift 841590
  have htrace : WordTrace (prefixWord ++ tailWord_841590) baseStart_841590 baseEnd_841590 := by
    simpa [prefixWord, tailWord_841590, baseEnd_841590] using wordTrace_append hprefix tailTrace_841590
  have hstable : (prefixWord ++ tailWord_841590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841590).length < 2 ^ (prefixWord ++ tailWord_841590).sum := by decide
  have hdescent : baseEnd_841590 < baseStart_841590 := by decide
  rcases family_descends (prefixWord ++ tailWord_841590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841652 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 4]
def baseStart_841652 : Nat := 118140960795 + 841652 * 2 ^ 59
def prefixEnd_841652 : Nat := 4983230072969 + 3 ^ 40 * 841652 * 2
def baseEnd_841652 : Nat := 384152906504930014559395

theorem tailTrace_841652 : CollatzResearch.WordTrace tailWord_841652 prefixEnd_841652 384152906504930014559395 := by
  unfold tailWord_841652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348785173423010781383605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20465046897897347708511473 15348785173423010781383605)
  ·
    refine ⟨1438948610008407260754713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15348785173423010781383605 1438948610008407260754713)
    ·
      refine ⟨1079211457506305445566035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1438948610008407260754713 1079211457506305445566035)
      ·
        refine ⟨1618817186259458168349053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1079211457506305445566035 1618817186259458168349053)
        ·
          refine ⟨607056444847296813130895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1618817186259458168349053 607056444847296813130895)
          ·
            refine ⟨910584667270945219696343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607056444847296813130895 910584667270945219696343)
            ·
              refine ⟨1365877000906417829544515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910584667270945219696343 1365877000906417829544515)
              ·
                refine ⟨2048815501359626744316773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365877000906417829544515 2048815501359626744316773)
                ·
                  refine ⟨384152906504930014559395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2048815501359626744316773 384152906504930014559395)
                  ·
                    rfl

theorem cell20_841652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_841652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841652 prefixEnd_841652 := by exact prefixLift 841652
  have htrace : WordTrace (prefixWord ++ tailWord_841652) baseStart_841652 baseEnd_841652 := by
    simpa [prefixWord, tailWord_841652, baseEnd_841652] using wordTrace_append hprefix tailTrace_841652
  have hstable : (prefixWord ++ tailWord_841652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841652).length < 2 ^ (prefixWord ++ tailWord_841652).sum := by decide
  have hdescent : baseEnd_841652 < baseStart_841652 := by decide
  rcases family_descends (prefixWord ++ tailWord_841652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841653 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 5]
def baseStart_841653 : Nat := 118140960795 + 841653 * 2 ^ 59
def prefixEnd_841653 : Nat := 4983230072969 + 3 ^ 40 * 841653 * 2
def baseEnd_841653 : Nat := 384153362932178455526057

theorem tailTrace_841653 : CollatzResearch.WordTrace tailWord_841653 prefixEnd_841653 384153362932178455526057 := by
  unfold tailWord_841653
  simp only [CollatzResearch.WordTrace]
  refine ⟨30697606819842398733553613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20465071213228265822369075 30697606819842398733553613)
  ·
    refine ⟨11511602557440899525082605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30697606819842398733553613 11511602557440899525082605)
    ·
      refine ⟨4316850959040337321905977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11511602557440899525082605 4316850959040337321905977)
      ·
        refine ⟨3237638219280252991429483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4316850959040337321905977 3237638219280252991429483)
        ·
          refine ⟨4856457328920379487144225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3237638219280252991429483 4856457328920379487144225)
          ·
            refine ⟨3642342996690284615358169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4856457328920379487144225 3642342996690284615358169)
            ·
              refine ⟨2731757247517713461518627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3642342996690284615358169 2731757247517713461518627)
              ·
                refine ⟨4097635871276570192277941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731757247517713461518627 4097635871276570192277941)
                ·
                  refine ⟨384153362932178455526057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4097635871276570192277941 384153362932178455526057)
                  ·
                    rfl

theorem cell20_841653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_841653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841653 prefixEnd_841653 := by exact prefixLift 841653
  have htrace : WordTrace (prefixWord ++ tailWord_841653) baseStart_841653 baseEnd_841653 := by
    simpa [prefixWord, tailWord_841653, baseEnd_841653] using wordTrace_append hprefix tailTrace_841653
  have hstable : (prefixWord ++ tailWord_841653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841653).length < 2 ^ (prefixWord ++ tailWord_841653).sum := by decide
  have hdescent : baseEnd_841653 < baseStart_841653 := by decide
  rcases family_descends (prefixWord ++ tailWord_841653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841656 : List Nat := [2, 1, 2, 1, 2, 3, 5, 2, 2]
def baseStart_841656 : Nat := 118140960795 + 841656 * 2 ^ 59
def prefixEnd_841656 : Nat := 4983230072969 + 3 ^ 40 * 841656 * 2
def baseEnd_841656 : Nat := 384154732213923778426045

theorem tailTrace_841656 : CollatzResearch.WordTrace tailWord_841656 prefixEnd_841656 384154732213923778426045 := by
  unfold tailWord_841656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348858119415765122956411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20465144159221020163941881 15348858119415765122956411)
  ·
    refine ⟨23023287179123647684434617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15348858119415765122956411 23023287179123647684434617)
    ·
      refine ⟨17267465384342735763325963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23023287179123647684434617 17267465384342735763325963)
      ·
        refine ⟨25901198076514103644988945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17267465384342735763325963 25901198076514103644988945)
        ·
          refine ⟨19425898557385577733741709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25901198076514103644988945 19425898557385577733741709)
          ·
            refine ⟨7284711959019591650153141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19425898557385577733741709 7284711959019591650153141)
            ·
              refine ⟨682941746158086717201857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7284711959019591650153141 682941746158086717201857)
              ·
                refine ⟨512206309618565037901393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682941746158086717201857 512206309618565037901393)
                ·
                  refine ⟨384154732213923778426045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512206309618565037901393 384154732213923778426045)
                  ·
                    rfl

theorem cell20_841656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_841656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841656 prefixEnd_841656 := by exact prefixLift 841656
  have htrace : WordTrace (prefixWord ++ tailWord_841656) baseStart_841656 baseEnd_841656 := by
    simpa [prefixWord, tailWord_841656, baseEnd_841656] using wordTrace_append hprefix tailTrace_841656
  have hstable : (prefixWord ++ tailWord_841656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841656).length < 2 ^ (prefixWord ++ tailWord_841656).sum := by decide
  have hdescent : baseEnd_841656 < baseStart_841656 := by decide
  rcases family_descends (prefixWord ++ tailWord_841656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841712 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_841712 : Nat := 118140960795 + 841712 * 2 ^ 59
def prefixEnd_841712 : Nat := 4983230072969 + 3 ^ 40 * 841712 * 2
def baseEnd_841712 : Nat := 384180292139836472559149

theorem tailTrace_841712 : CollatzResearch.WordTrace tailWord_841712 prefixEnd_841712 384180292139836472559149 := by
  unfold tailWord_841712
  simp only [CollatzResearch.WordTrace]
  refine ⟨15349879363314325904975695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20466505817752434539967593 15349879363314325904975695)
  ·
    refine ⟨23024819044971488857463543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15349879363314325904975695 23024819044971488857463543)
    ·
      refine ⟨34537228567457233286195315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23024819044971488857463543 34537228567457233286195315)
      ·
        refine ⟨51805842851185849929292973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34537228567457233286195315 51805842851185849929292973)
        ·
          refine ⟨19427191069194693723484865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51805842851185849929292973 19427191069194693723484865)
          ·
            refine ⟨14570393301896020292613649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19427191069194693723484865 14570393301896020292613649)
            ·
              refine ⟨10927794976422015219460237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14570393301896020292613649 10927794976422015219460237)
              ·
                refine ⟨4097923116158255707297589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10927794976422015219460237 4097923116158255707297589)
                ·
                  refine ⟨384180292139836472559149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4097923116158255707297589 384180292139836472559149)
                  ·
                    rfl

theorem cell20_841712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_841712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841712 prefixEnd_841712 := by exact prefixLift 841712
  have htrace : WordTrace (prefixWord ++ tailWord_841712) baseStart_841712 baseEnd_841712 := by
    simpa [prefixWord, tailWord_841712, baseEnd_841712] using wordTrace_append hprefix tailTrace_841712
  have hstable : (prefixWord ++ tailWord_841712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841712).length < 2 ^ (prefixWord ++ tailWord_841712).sum := by decide
  have hdescent : baseEnd_841712 < baseStart_841712 := by decide
  rcases family_descends (prefixWord ++ tailWord_841712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841718 : List Nat := [5, 1, 1, 1, 5, 1, 1, 5]
def baseStart_841718 : Nat := 118140960795 + 841718 * 2 ^ 59
def prefixEnd_841718 : Nat := 4983230072969 + 3 ^ 40 * 841718 * 2
def baseEnd_841718 : Nat := 128061010234442372786375

theorem tailTrace_841718 : CollatzResearch.WordTrace tailWord_841718 prefixEnd_841718 128061010234442372786375 := by
  unfold tailWord_841718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918748597787932177166863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20466651709737943223113205 1918748597787932177166863)
  ·
    refine ⟨2878122896681898265750295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1918748597787932177166863 2878122896681898265750295)
    ·
      refine ⟨4317184345022847398625443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2878122896681898265750295 4317184345022847398625443)
      ·
        refine ⟨6475776517534271097938165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4317184345022847398625443 6475776517534271097938165)
        ·
          refine ⟨607104048518837915431703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6475776517534271097938165 607104048518837915431703)
          ·
            refine ⟨910656072778256873147555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607104048518837915431703 910656072778256873147555)
            ·
              refine ⟨1365984109167385309721333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910656072778256873147555 1365984109167385309721333)
              ·
                refine ⟨128061010234442372786375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1365984109167385309721333 128061010234442372786375)
                ·
                  rfl

theorem cell20_841718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_841718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841718 prefixEnd_841718 := by exact prefixLift 841718
  have htrace : WordTrace (prefixWord ++ tailWord_841718) baseStart_841718 baseEnd_841718 := by
    simpa [prefixWord, tailWord_841718, baseEnd_841718] using wordTrace_append hprefix tailTrace_841718
  have hstable : (prefixWord ++ tailWord_841718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841718).length < 2 ^ (prefixWord ++ tailWord_841718).sum := by decide
  have hdescent : baseEnd_841718 < baseStart_841718 := by decide
  rcases family_descends (prefixWord ++ tailWord_841718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841719 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 10]
def baseStart_841719 : Nat := 118140960795 + 841719 * 2 ^ 59
def prefixEnd_841719 : Nat := 4983230072969 + 3 ^ 40 * 841719 * 2
def baseEnd_841719 : Nat := 384183487130575559325787

theorem tailTrace_841719 : CollatzResearch.WordTrace tailWord_841719 prefixEnd_841719 384183487130575559325787 := by
  unfold tailWord_841719
  simp only [CollatzResearch.WordTrace]
  refine ⟨30700014037603292005456211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20466676025068861336970807 30700014037603292005456211)
  ·
    refine ⟨46050021056404938008184317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30700014037603292005456211 46050021056404938008184317)
    ·
      refine ⟨17268757896151851753069119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46050021056404938008184317 17268757896151851753069119)
      ·
        refine ⟨25903136844227777629603679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17268757896151851753069119 25903136844227777629603679)
        ·
          refine ⟨38854705266341666444405519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25903136844227777629603679 38854705266341666444405519)
          ·
            refine ⟨58282057899512499666608279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38854705266341666444405519 58282057899512499666608279)
            ·
              refine ⟨87423086849268749499912419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58282057899512499666608279 87423086849268749499912419)
              ·
                refine ⟨131134630273903124249868629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87423086849268749499912419 131134630273903124249868629)
                ·
                  refine ⟨384183487130575559325787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 131134630273903124249868629 384183487130575559325787)
                  ·
                    rfl

theorem cell20_841719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_841719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841719 prefixEnd_841719 := by exact prefixLift 841719
  have htrace : WordTrace (prefixWord ++ tailWord_841719) baseStart_841719 baseEnd_841719 := by
    simpa [prefixWord, tailWord_841719, baseEnd_841719] using wordTrace_append hprefix tailTrace_841719
  have hstable : (prefixWord ++ tailWord_841719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841719).length < 2 ^ (prefixWord ++ tailWord_841719).sum := by decide
  have hdescent : baseEnd_841719 < baseStart_841719 := by decide
  rcases family_descends (prefixWord ++ tailWord_841719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841729 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 3]
def baseStart_841729 : Nat := 118140960795 + 841729 * 2 ^ 59
def prefixEnd_841729 : Nat := 4983230072969 + 3 ^ 40 * 841729 * 2
def baseEnd_841729 : Nat := 384188051403059968992413

theorem tailTrace_841729 : CollatzResearch.WordTrace tailWord_841729 prefixEnd_841729 384188051403059968992413 := by
  unfold tailWord_841729
  simp only [CollatzResearch.WordTrace]
  refine ⟨30700378767567063713320241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20466919178378042475546827 30700378767567063713320241)
  ·
    refine ⟨23025284075675297784990181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30700378767567063713320241 23025284075675297784990181)
    ·
      refine ⟨4317240764189118334685659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23025284075675297784990181 4317240764189118334685659)
      ·
        refine ⟨6475861146283677502028489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4317240764189118334685659 6475861146283677502028489)
        ·
          refine ⟨4856895859712758126521367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6475861146283677502028489 4856895859712758126521367)
          ·
            refine ⟨7285343789569137189782051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4856895859712758126521367 7285343789569137189782051)
            ·
              refine ⟨10928015684353705784673077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7285343789569137189782051 10928015684353705784673077)
              ·
                refine ⟨1024501470408159917313101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10928015684353705784673077 1024501470408159917313101)
                ·
                  refine ⟨384188051403059968992413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024501470408159917313101 384188051403059968992413)
                  ·
                    rfl

theorem cell20_841729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_841729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841729 prefixEnd_841729 := by exact prefixLift 841729
  have htrace : WordTrace (prefixWord ++ tailWord_841729) baseStart_841729 baseEnd_841729 := by
    simpa [prefixWord, tailWord_841729, baseEnd_841729] using wordTrace_append hprefix tailTrace_841729
  have hstable : (prefixWord ++ tailWord_841729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841729).length < 2 ^ (prefixWord ++ tailWord_841729).sum := by decide
  have hdescent : baseEnd_841729 < baseStart_841729 := by decide
  rcases family_descends (prefixWord ++ tailWord_841729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841732 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 4]
def baseStart_841732 : Nat := 118140960795 + 841732 * 2 ^ 59
def prefixEnd_841732 : Nat := 4983230072969 + 3 ^ 40 * 841732 * 2
def baseEnd_841732 : Nat := 384189420684805291892401

theorem tailTrace_841732 : CollatzResearch.WordTrace tailWord_841732 prefixEnd_841732 384189420684805291892401 := by
  unfold tailWord_841732
  simp only [CollatzResearch.WordTrace]
  refine ⟨15350244093278097612839725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20466992124370796817119633 15350244093278097612839725)
  ·
    refine ⟨5756341534979286604814897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15350244093278097612839725 5756341534979286604814897)
    ·
      refine ⟨4317256151234464953611173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5756341534979286604814897 4317256151234464953611173)
      ·
        refine ⟨809485528356462178802095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4317256151234464953611173 809485528356462178802095)
        ·
          refine ⟨1214228292534693268203143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809485528356462178802095 1214228292534693268203143)
          ·
            refine ⟨1821342438802039902304715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214228292534693268203143 1821342438802039902304715)
            ·
              refine ⟨2732013658203059853457073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821342438802039902304715 2732013658203059853457073)
              ·
                refine ⟨2049010243652294890092805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2732013658203059853457073 2049010243652294890092805)
                ·
                  refine ⟨384189420684805291892401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049010243652294890092805 384189420684805291892401)
                  ·
                    rfl

theorem cell20_841732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_841732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841732 prefixEnd_841732 := by exact prefixLift 841732
  have htrace : WordTrace (prefixWord ++ tailWord_841732) baseStart_841732 baseEnd_841732 := by
    simpa [prefixWord, tailWord_841732, baseEnd_841732] using wordTrace_append hprefix tailTrace_841732
  have hstable : (prefixWord ++ tailWord_841732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841732).length < 2 ^ (prefixWord ++ tailWord_841732).sum := by decide
  have hdescent : baseEnd_841732 < baseStart_841732 := by decide
  rcases family_descends (prefixWord ++ tailWord_841732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841736 : List Nat := [2, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_841736 : Nat := 118140960795 + 841736 * 2 ^ 59
def prefixEnd_841736 : Nat := 4983230072969 + 3 ^ 40 * 841736 * 2
def baseEnd_841736 : Nat := 384191246393799055759051

theorem tailTrace_841736 : CollatzResearch.WordTrace tailWord_841736 prefixEnd_841736 384191246393799055759051 := by
  unfold tailWord_841736
  simp only [CollatzResearch.WordTrace]
  refine ⟨15350317039270851954412531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20467089385694469272550041 15350317039270851954412531)
  ·
    refine ⟨23025475558906277931618797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15350317039270851954412531 23025475558906277931618797)
    ·
      refine ⟨8634553334589854224357049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23025475558906277931618797 8634553334589854224357049)
      ·
        refine ⟨6475915000942390668267787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8634553334589854224357049 6475915000942390668267787)
        ·
          refine ⟨9713872501413586002401681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6475915000942390668267787 9713872501413586002401681)
          ·
            refine ⟨7285404376060189501801261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9713872501413586002401681 7285404376060189501801261)
            ·
              refine ⟨2732026641022571063175473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7285404376060189501801261 2732026641022571063175473)
              ·
                refine ⟨2049019980766928297381605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2732026641022571063175473 2049019980766928297381605)
                ·
                  refine ⟨384191246393799055759051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049019980766928297381605 384191246393799055759051)
                  ·
                    rfl

theorem cell20_841736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_841736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841736 prefixEnd_841736 := by exact prefixLift 841736
  have htrace : WordTrace (prefixWord ++ tailWord_841736) baseStart_841736 baseEnd_841736 := by
    simpa [prefixWord, tailWord_841736, baseEnd_841736] using wordTrace_append hprefix tailTrace_841736
  have hstable : (prefixWord ++ tailWord_841736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841736).length < 2 ^ (prefixWord ++ tailWord_841736).sum := by decide
  have hdescent : baseEnd_841736 < baseStart_841736 := by decide
  rcases family_descends (prefixWord ++ tailWord_841736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841770 : List Nat := [3, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_841770 : Nat := 118140960795 + 841770 * 2 ^ 59
def prefixEnd_841770 : Nat := 4983230072969 + 3 ^ 40 * 841770 * 2
def baseEnd_841770 : Nat := 384206764920246048625579

theorem tailTrace_841770 : CollatzResearch.WordTrace tailWord_841770 prefixEnd_841770 384206764920246048625579 := by
  unfold tailWord_841770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7675468540104631928890691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20467916106945685143708509 7675468540104631928890691)
  ·
    refine ⟨11513202810156947893336037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7675468540104631928890691 11513202810156947893336037)
    ·
      refine ⟨2158725526904427730000507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11513202810156947893336037 2158725526904427730000507)
      ·
        refine ⟨3238088290356641595000761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158725526904427730000507 3238088290356641595000761)
        ·
          refine ⟨2428566217767481196250571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3238088290356641595000761 2428566217767481196250571)
          ·
            refine ⟨3642849326651221794375857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428566217767481196250571 3642849326651221794375857)
            ·
              refine ⟨2732136994988416345781893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3642849326651221794375857 2732136994988416345781893)
              ·
                refine ⟨512275686560328064834105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2732136994988416345781893 512275686560328064834105)
                ·
                  refine ⟨384206764920246048625579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512275686560328064834105 384206764920246048625579)
                  ·
                    rfl

theorem cell20_841770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_841770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841770 prefixEnd_841770 := by exact prefixLift 841770
  have htrace : WordTrace (prefixWord ++ tailWord_841770) baseStart_841770 baseEnd_841770 := by
    simpa [prefixWord, tailWord_841770, baseEnd_841770] using wordTrace_append hprefix tailTrace_841770
  have hstable : (prefixWord ++ tailWord_841770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841770).length < 2 ^ (prefixWord ++ tailWord_841770).sum := by decide
  have hdescent : baseEnd_841770 < baseStart_841770 := by decide
  rcases family_descends (prefixWord ++ tailWord_841770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841780 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 3]
def baseStart_841780 : Nat := 118140960795 + 841780 * 2 ^ 59
def prefixEnd_841780 : Nat := 4983230072969 + 3 ^ 40 * 841780 * 2
def baseEnd_841780 : Nat := 384211329192730458292205

theorem tailTrace_841780 : CollatzResearch.WordTrace tailWord_841780 prefixEnd_841780 384211329192730458292205 := by
  unfold tailWord_841780
  simp only [CollatzResearch.WordTrace]
  refine ⟨15351119445191149711713397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20468159260254866282284529 15351119445191149711713397)
  ·
    refine ⟨1439167447986670285473131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15351119445191149711713397 1439167447986670285473131)
    ·
      refine ⟨2158751171980005428209697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1439167447986670285473131 2158751171980005428209697)
      ·
        refine ⟨1619063378985004071157273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2158751171980005428209697 1619063378985004071157273)
        ·
          refine ⟨1214297534238753053367955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1619063378985004071157273 1214297534238753053367955)
          ·
            refine ⟨1821446301358129580051933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214297534238753053367955 1821446301358129580051933)
            ·
              refine ⟨683042363009298592519475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1821446301358129580051933 683042363009298592519475)
              ·
                refine ⟨1024563544513947888779213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683042363009298592519475 1024563544513947888779213)
                ·
                  refine ⟨384211329192730458292205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024563544513947888779213 384211329192730458292205)
                  ·
                    rfl

theorem cell20_841780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_841780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841780 prefixEnd_841780 := by exact prefixLift 841780
  have htrace : WordTrace (prefixWord ++ tailWord_841780) baseStart_841780 baseEnd_841780 := by
    simpa [prefixWord, tailWord_841780, baseEnd_841780] using wordTrace_append hprefix tailTrace_841780
  have hstable : (prefixWord ++ tailWord_841780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841780).length < 2 ^ (prefixWord ++ tailWord_841780).sum := by decide
  have hdescent : baseEnd_841780 < baseStart_841780 := by decide
  rcases family_descends (prefixWord ++ tailWord_841780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841795 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_841795 : Nat := 118140960795 + 841795 * 2 ^ 59
def prefixEnd_841795 : Nat := 4983230072969 + 3 ^ 40 * 841795 * 2
def baseEnd_841795 : Nat := 384218175601457072792143

theorem tailTrace_841795 : CollatzResearch.WordTrace tailWord_841795 prefixEnd_841795 384218175601457072792143 := by
  unfold tailWord_841795
  simp only [CollatzResearch.WordTrace]
  refine ⟨30702785985327956985222839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20468523990218637990148559 30702785985327956985222839)
  ·
    refine ⟨46054178977991935477834259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30702785985327956985222839 46054178977991935477834259)
    ·
      refine ⟨69081268466987903216751389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46054178977991935477834259 69081268466987903216751389)
      ·
        refine ⟨25905475675120463706281771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69081268466987903216751389 25905475675120463706281771)
        ·
          refine ⟨38858213512680695559422657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25905475675120463706281771 38858213512680695559422657)
          ·
            refine ⟨29143660134510521669566993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38858213512680695559422657 29143660134510521669566993)
            ·
              refine ⟨21857745100882891252175245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29143660134510521669566993 21857745100882891252175245)
              ·
                refine ⟨8196654412831084219565717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21857745100882891252175245 8196654412831084219565717)
                ·
                  refine ⟨384218175601457072792143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8196654412831084219565717 384218175601457072792143)
                  ·
                    rfl

theorem cell20_841795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_841795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841795 prefixEnd_841795 := by exact prefixLift 841795
  have htrace : WordTrace (prefixWord ++ tailWord_841795) baseStart_841795 baseEnd_841795 := by
    simpa [prefixWord, tailWord_841795, baseEnd_841795] using wordTrace_append hprefix tailTrace_841795
  have hstable : (prefixWord ++ tailWord_841795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841795).length < 2 ^ (prefixWord ++ tailWord_841795).sum := by decide
  have hdescent : baseEnd_841795 < baseStart_841795 := by decide
  rcases family_descends (prefixWord ++ tailWord_841795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841805 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 7]
def baseStart_841805 : Nat := 118140960795 + 841805 * 2 ^ 59
def prefixEnd_841805 : Nat := 4983230072969 + 3 ^ 40 * 841805 * 2
def baseEnd_841805 : Nat := 384222739873941482458769

theorem tailTrace_841805 : CollatzResearch.WordTrace tailWord_841805 prefixEnd_841805 384222739873941482458769 := by
  unfold tailWord_841805
  simp only [CollatzResearch.WordTrace]
  refine ⟨30703150715291728693086869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20468767143527819128724579 30703150715291728693086869)
  ·
    refine ⟨1439210189779299782488447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30703150715291728693086869 1439210189779299782488447)
    ·
      refine ⟨2158815284668949673732671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1439210189779299782488447 2158815284668949673732671)
      ·
        refine ⟨3238222927003424510599007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158815284668949673732671 3238222927003424510599007)
        ·
          refine ⟨4857334390505136765898511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238222927003424510599007 4857334390505136765898511)
          ·
            refine ⟨7286001585757705148847767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4857334390505136765898511 7286001585757705148847767)
            ·
              refine ⟨10929002378636557723271651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286001585757705148847767 10929002378636557723271651)
              ·
                refine ⟨16393503567954836584907477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929002378636557723271651 16393503567954836584907477)
                ·
                  refine ⟨384222739873941482458769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16393503567954836584907477 384222739873941482458769)
                  ·
                    rfl

theorem cell20_841805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_841805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841805 prefixEnd_841805 := by exact prefixLift 841805
  have htrace : WordTrace (prefixWord ++ tailWord_841805) baseStart_841805 baseEnd_841805 := by
    simpa [prefixWord, tailWord_841805, baseEnd_841805] using wordTrace_append hprefix tailTrace_841805
  have hstable : (prefixWord ++ tailWord_841805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841805).length < 2 ^ (prefixWord ++ tailWord_841805).sum := by decide
  have hdescent : baseEnd_841805 < baseStart_841805 := by decide
  rcases family_descends (prefixWord ++ tailWord_841805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841829 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 4]
def baseStart_841829 : Nat := 118140960795 + 841829 * 2 ^ 59
def prefixEnd_841829 : Nat := 4983230072969 + 3 ^ 40 * 841829 * 2
def baseEnd_841829 : Nat := 384233694127904065658671

theorem tailTrace_841829 : CollatzResearch.WordTrace tailWord_841829 prefixEnd_841829 384233694127904065658671 := by
  unfold tailWord_841829
  simp only [CollatzResearch.WordTrace]
  refine ⟨30704026067204780791960541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20469350711469853861307027 30704026067204780791960541)
  ·
    refine ⟨11514009775201792796985203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30704026067204780791960541 11514009775201792796985203)
    ·
      refine ⟨17271014662802689195477805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11514009775201792796985203 17271014662802689195477805)
      ·
        refine ⟨6476630498551008448304177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17271014662802689195477805 6476630498551008448304177)
        ·
          refine ⟨4857472873913256336228133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6476630498551008448304177 4857472873913256336228133)
          ·
            refine ⟨910776163858735563042775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4857472873913256336228133 910776163858735563042775)
            ·
              refine ⟨1366164245788103344564163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910776163858735563042775 1366164245788103344564163)
              ·
                refine ⟨2049246368682155016846245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366164245788103344564163 2049246368682155016846245)
                ·
                  refine ⟨384233694127904065658671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049246368682155016846245 384233694127904065658671)
                  ·
                    rfl

theorem cell20_841829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_841829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841829 prefixEnd_841829 := by exact prefixLift 841829
  have htrace : WordTrace (prefixWord ++ tailWord_841829) baseStart_841829 baseEnd_841829 := by
    simpa [prefixWord, tailWord_841829, baseEnd_841829] using wordTrace_append hprefix tailTrace_841829
  have hstable : (prefixWord ++ tailWord_841829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841829).length < 2 ^ (prefixWord ++ tailWord_841829).sum := by decide
  have hdescent : baseEnd_841829 < baseStart_841829 := by decide
  rcases family_descends (prefixWord ++ tailWord_841829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841880 : List Nat := [2, 1, 2, 4, 4, 1, 2, 2, 2]
def baseStart_841880 : Nat := 118140960795 + 841880 * 2 ^ 59
def prefixEnd_841880 : Nat := 4983230072969 + 3 ^ 40 * 841880 * 2
def baseEnd_841880 : Nat := 384256971917574554958463

theorem tailTrace_841880 : CollatzResearch.WordTrace tailWord_841880 prefixEnd_841880 384256971917574554958463 := by
  unfold tailWord_841880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15352943095010008251033547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20470590793346677668044729 15352943095010008251033547)
  ·
    refine ⟨23029414642515012376550321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15352943095010008251033547 23029414642515012376550321)
    ·
      refine ⟨17272060981886259282412741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23029414642515012376550321 17272060981886259282412741)
      ·
        refine ⟨3238511434103673615452389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17272060981886259282412741 3238511434103673615452389)
        ·
          refine ⟨607220893894438802897323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3238511434103673615452389 607220893894438802897323)
          ·
            refine ⟨910831340841658204345985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607220893894438802897323 910831340841658204345985)
            ·
              refine ⟨683123505631243653259489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910831340841658204345985 683123505631243653259489)
              ·
                refine ⟨512342629223432739944617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683123505631243653259489 512342629223432739944617)
                ·
                  refine ⟨384256971917574554958463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512342629223432739944617 384256971917574554958463)
                  ·
                    rfl

theorem cell20_841880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_841880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841880 prefixEnd_841880 := by exact prefixLift 841880
  have htrace : WordTrace (prefixWord ++ tailWord_841880) baseStart_841880 baseEnd_841880 := by
    simpa [prefixWord, tailWord_841880, baseEnd_841880] using wordTrace_append hprefix tailTrace_841880
  have hstable : (prefixWord ++ tailWord_841880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841880).length < 2 ^ (prefixWord ++ tailWord_841880).sum := by decide
  have hdescent : baseEnd_841880 < baseStart_841880 := by decide
  rcases family_descends (prefixWord ++ tailWord_841880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841905 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 4]
def baseStart_841905 : Nat := 118140960795 + 841905 * 2 ^ 59
def prefixEnd_841905 : Nat := 4983230072969 + 3 ^ 40 * 841905 * 2
def baseEnd_841905 : Nat := 384268382598785579125027

theorem tailTrace_841905 : CollatzResearch.WordTrace tailWord_841905 prefixEnd_841905 384268382598785579125027 := by
  unfold tailWord_841905
  simp only [CollatzResearch.WordTrace]
  refine ⟨30706798014929445771727169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20471198676619630514484779 30706798014929445771727169)
  ·
    refine ⟨23030098511197084328795377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30706798014929445771727169 23030098511197084328795377)
    ·
      refine ⟨17272573883397813246596533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23030098511197084328795377 17272573883397813246596533)
      ·
        refine ⟨1619303801568544991868425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17272573883397813246596533 1619303801568544991868425)
        ·
          refine ⟨1214477851176408743901319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1619303801568544991868425 1214477851176408743901319)
          ·
            refine ⟨1821716776764613115851979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214477851176408743901319 1821716776764613115851979)
            ·
              refine ⟨2732575165146919673777969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1821716776764613115851979 2732575165146919673777969)
              ·
                refine ⟨2049431373860189755333477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2732575165146919673777969 2049431373860189755333477)
                ·
                  refine ⟨384268382598785579125027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049431373860189755333477 384268382598785579125027)
                  ·
                    rfl

theorem cell20_841905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_841905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841905 prefixEnd_841905 := by exact prefixLift 841905
  have htrace : WordTrace (prefixWord ++ tailWord_841905) baseStart_841905 baseEnd_841905 := by
    simpa [prefixWord, tailWord_841905, baseEnd_841905] using wordTrace_append hprefix tailTrace_841905
  have hstable : (prefixWord ++ tailWord_841905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841905).length < 2 ^ (prefixWord ++ tailWord_841905).sum := by decide
  have hdescent : baseEnd_841905 < baseStart_841905 := by decide
  rcases family_descends (prefixWord ++ tailWord_841905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841932 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 3]
def baseStart_841932 : Nat := 118140960795 + 841932 * 2 ^ 59
def prefixEnd_841932 : Nat := 4983230072969 + 3 ^ 40 * 841932 * 2
def baseEnd_841932 : Nat := 384280706134493485224917

theorem tailTrace_841932 : CollatzResearch.WordTrace tailWord_841932 prefixEnd_841932 384280706134493485224917 := by
  unfold tailWord_841932
  simp only [CollatzResearch.WordTrace]
  refine ⟨15353891392915814691480025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20471855190554419588640033 15353891392915814691480025)
  ·
    refine ⟨11515418544686861018610019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15353891392915814691480025 11515418544686861018610019)
    ·
      refine ⟨17273127817030291527915029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11515418544686861018610019 17273127817030291527915029)
      ·
        refine ⟨809677866423294915371017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17273127817030291527915029 809677866423294915371017)
        ·
          refine ⟨607258399817471186528263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 809677866423294915371017 607258399817471186528263)
          ·
            refine ⟨910887599726206779792395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607258399817471186528263 910887599726206779792395)
            ·
              refine ⟨1366331399589310169688593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910887599726206779792395 1366331399589310169688593)
              ·
                refine ⟨1024748549691982627266445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366331399589310169688593 1024748549691982627266445)
                ·
                  refine ⟨384280706134493485224917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024748549691982627266445 384280706134493485224917)
                  ·
                    rfl

theorem cell20_841932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_841932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841932 prefixEnd_841932 := by exact prefixLift 841932
  have htrace : WordTrace (prefixWord ++ tailWord_841932) baseStart_841932 baseEnd_841932 := by
    simpa [prefixWord, tailWord_841932, baseEnd_841932] using wordTrace_append hprefix tailTrace_841932
  have hstable : (prefixWord ++ tailWord_841932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841932).length < 2 ^ (prefixWord ++ tailWord_841932).sum := by decide
  have hdescent : baseEnd_841932 < baseStart_841932 := by decide
  rcases family_descends (prefixWord ++ tailWord_841932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841947 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 4]
def baseStart_841947 : Nat := 118140960795 + 841947 * 2 ^ 59
def prefixEnd_841947 : Nat := 4983230072969 + 3 ^ 40 * 841947 * 2
def baseEnd_841947 : Nat := 384287552543220099724855

theorem tailTrace_841947 : CollatzResearch.WordTrace tailWord_841947 prefixEnd_841947 384287552543220099724855 := by
  unfold tailWord_841947
  simp only [CollatzResearch.WordTrace]
  refine ⟨30708329880777286944756095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20472219920518191296504063 30708329880777286944756095)
  ·
    refine ⟨46062494821165930417134143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30708329880777286944756095 46062494821165930417134143)
    ·
      refine ⟨69093742231748895625701215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46062494821165930417134143 69093742231748895625701215)
      ·
        refine ⟨103640613347623343438551823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69093742231748895625701215 103640613347623343438551823)
        ·
          refine ⟨155460920021435015157827735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103640613347623343438551823 155460920021435015157827735)
          ·
            refine ⟨233191380032152522736741603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155460920021435015157827735 233191380032152522736741603)
            ·
              refine ⟨349787070048228784105112405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233191380032152522736741603 349787070048228784105112405)
              ·
                refine ⟨2049533613563840531865893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 349787070048228784105112405 2049533613563840531865893)
                ·
                  refine ⟨384287552543220099724855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049533613563840531865893 384287552543220099724855)
                  ·
                    rfl

theorem cell20_841947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 4].length) (baseStart_841947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841947 prefixEnd_841947 := by exact prefixLift 841947
  have htrace : WordTrace (prefixWord ++ tailWord_841947) baseStart_841947 baseEnd_841947 := by
    simpa [prefixWord, tailWord_841947, baseEnd_841947] using wordTrace_append hprefix tailTrace_841947
  have hstable : (prefixWord ++ tailWord_841947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841947).length < 2 ^ (prefixWord ++ tailWord_841947).sum := by decide
  have hdescent : baseEnd_841947 < baseStart_841947 := by decide
  rcases family_descends (prefixWord ++ tailWord_841947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841978 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_841978 : Nat := 118140960795 + 841978 * 2 ^ 59
def prefixEnd_841978 : Nat := 4983230072969 + 3 ^ 40 * 841978 * 2
def baseEnd_841978 : Nat := 384301701787921769691395

theorem tailTrace_841978 : CollatzResearch.WordTrace tailWord_841978 prefixEnd_841978 384301701787921769691395 := by
  unfold tailWord_841978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7677365135916244809783647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20472973695776652826089725 7677365135916244809783647)
  ·
    refine ⟨11516047703874367214675471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7677365135916244809783647 11516047703874367214675471)
    ·
      refine ⟨17274071555811550822013207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11516047703874367214675471 17274071555811550822013207)
      ·
        refine ⟨25911107333717326233019811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17274071555811550822013207 25911107333717326233019811)
        ·
          refine ⟨38866661000575989349529717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25911107333717326233019811 38866661000575989349529717)
          ·
            refine ⟨3643749468803999001518411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38866661000575989349529717 3643749468803999001518411)
            ·
              refine ⟨5465624203205998502277617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643749468803999001518411 5465624203205998502277617)
              ·
                refine ⟨4099218152404498876708213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5465624203205998502277617 4099218152404498876708213)
                ·
                  refine ⟨384301701787921769691395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4099218152404498876708213 384301701787921769691395)
                  ·
                    rfl

theorem cell20_841978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_841978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841978 prefixEnd_841978 := by exact prefixLift 841978
  have htrace : WordTrace (prefixWord ++ tailWord_841978) baseStart_841978 baseEnd_841978 := by
    simpa [prefixWord, tailWord_841978, baseEnd_841978] using wordTrace_append hprefix tailTrace_841978
  have hstable : (prefixWord ++ tailWord_841978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841978).length < 2 ^ (prefixWord ++ tailWord_841978).sum := by decide
  have hdescent : baseEnd_841978 < baseStart_841978 := by decide
  rcases family_descends (prefixWord ++ tailWord_841978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841988 : List Nat := [2, 3, 2, 2, 3, 2, 6]
def baseStart_841988 : Nat := 118140960795 + 841988 * 2 ^ 59
def prefixEnd_841988 : Nat := 4983230072969 + 3 ^ 40 * 841988 * 2
def baseEnd_841988 : Nat := 42700696228934019928669

theorem tailTrace_841988 : CollatzResearch.WordTrace tailWord_841988 prefixEnd_841988 42700696228934019928669 := by
  unfold tailWord_841988
  simp only [CollatzResearch.WordTrace]
  refine ⟨15354912636814375473499309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20473216849085833964665745 15354912636814375473499309)
  ·
    refine ⟨5758092238805390802562241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15354912636814375473499309 5758092238805390802562241)
    ·
      refine ⟨4318569179104043101921681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5758092238805390802562241 4318569179104043101921681)
      ·
        refine ⟨3238926884328032326441261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4318569179104043101921681 3238926884328032326441261)
        ·
          refine ⟨1214597581623012122415473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3238926884328032326441261 1214597581623012122415473)
          ·
            refine ⟨910948186217259091811605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1214597581623012122415473 910948186217259091811605)
            ·
              refine ⟨42700696228934019928669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 910948186217259091811605 42700696228934019928669)
              ·
                rfl

theorem cell20_841988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 6].length) (baseStart_841988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841988 prefixEnd_841988 := by exact prefixLift 841988
  have htrace : WordTrace (prefixWord ++ tailWord_841988) baseStart_841988 baseEnd_841988 := by
    simpa [prefixWord, tailWord_841988, baseEnd_841988] using wordTrace_append hprefix tailTrace_841988
  have hstable : (prefixWord ++ tailWord_841988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841988).length < 2 ^ (prefixWord ++ tailWord_841988).sum := by decide
  have hdescent : baseEnd_841988 < baseStart_841988 := by decide
  rcases family_descends (prefixWord ++ tailWord_841988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_841998 : List Nat := [4, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_841998 : Nat := 118140960795 + 841998 * 2 ^ 59
def prefixEnd_841998 : Nat := 4983230072969 + 3 ^ 40 * 841998 * 2
def baseEnd_841998 : Nat := 384310830332890589024647

theorem tailTrace_841998 : CollatzResearch.WordTrace tailWord_841998 prefixEnd_841998 384310830332890589024647 := by
  unfold tailWord_841998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3838773750449065331857831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20473460002395015103241765 3838773750449065331857831)
  ·
    refine ⟨5758160625673597997786747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3838773750449065331857831 5758160625673597997786747)
    ·
      refine ⟨8637240938510396996680121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5758160625673597997786747 8637240938510396996680121)
      ·
        refine ⟨6477930703882797747510091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8637240938510396996680121 6477930703882797747510091)
        ·
          refine ⟨9716896055824196621265137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6477930703882797747510091 9716896055824196621265137)
          ·
            refine ⟨7287672041868147465948853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9716896055824196621265137 7287672041868147465948853)
            ·
              refine ⟨683219253925138824932705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7287672041868147465948853 683219253925138824932705)
              ·
                refine ⟨512414440443854118699529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683219253925138824932705 512414440443854118699529)
                ·
                  refine ⟨384310830332890589024647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512414440443854118699529 384310830332890589024647)
                  ·
                    rfl

theorem cell20_841998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_841998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_841998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_841998 prefixEnd_841998 := by exact prefixLift 841998
  have htrace : WordTrace (prefixWord ++ tailWord_841998) baseStart_841998 baseEnd_841998 := by
    simpa [prefixWord, tailWord_841998, baseEnd_841998] using wordTrace_append hprefix tailTrace_841998
  have hstable : (prefixWord ++ tailWord_841998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_841998).length < 2 ^ (prefixWord ++ tailWord_841998).sum := by decide
  have hdescent : baseEnd_841998 < baseStart_841998 := by decide
  rcases family_descends (prefixWord ++ tailWord_841998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842109 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 3]
def baseStart_842109 : Nat := 118140960795 + 842109 * 2 ^ 59
def prefixEnd_842109 : Nat := 4983230072969 + 3 ^ 40 * 842109 * 2
def baseEnd_842109 : Nat := 384361493757467536324193

theorem tailTrace_842109 : CollatzResearch.WordTrace tailWord_842109 prefixEnd_842109 384361493757467536324193 := by
  unfold tailWord_842109
  simp only [CollatzResearch.WordTrace]
  refine ⟨30714238506190388612153381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20476159004126925741435587 30714238506190388612153381)
  ·
    refine ⟨5758919719910697864778759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30714238506190388612153381 5758919719910697864778759)
    ·
      refine ⟨8638379579866046797168139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5758919719910697864778759 8638379579866046797168139)
      ·
        refine ⟨12957569369799070195752209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8638379579866046797168139 12957569369799070195752209)
        ·
          refine ⟨9718177027349302646814157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12957569369799070195752209 9718177027349302646814157)
          ·
            refine ⟨3644316385255988492555309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9718177027349302646814157 3644316385255988492555309)
            ·
              refine ⟨1366618644470995684708241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3644316385255988492555309 1366618644470995684708241)
              ·
                refine ⟨1024963983353246763531181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1366618644470995684708241 1024963983353246763531181)
                ·
                  refine ⟨384361493757467536324193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024963983353246763531181 384361493757467536324193)
                  ·
                    rfl

theorem cell20_842109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_842109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842109 prefixEnd_842109 := by exact prefixLift 842109
  have htrace : WordTrace (prefixWord ++ tailWord_842109) baseStart_842109 baseEnd_842109 := by
    simpa [prefixWord, tailWord_842109, baseEnd_842109] using wordTrace_append hprefix tailTrace_842109
  have hstable : (prefixWord ++ tailWord_842109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842109).length < 2 ^ (prefixWord ++ tailWord_842109).sum := by decide
  have hdescent : baseEnd_842109 < baseStart_842109 := by decide
  rcases family_descends (prefixWord ++ tailWord_842109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842116 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_842116 : Nat := 118140960795 + 842116 * 2 ^ 59
def prefixEnd_842116 : Nat := 4983230072969 + 3 ^ 40 * 842116 * 2
def baseEnd_842116 : Nat := 384364688748206623090831

theorem tailTrace_842116 : CollatzResearch.WordTrace tailWord_842116 prefixEnd_842116 384364688748206623090831 := by
  unfold tailWord_842116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15357246908582514403829101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20476329211443352538438801 15357246908582514403829101)
  ·
    refine ⟨5758967590718442901435913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15357246908582514403829101 5758967590718442901435913)
    ·
      refine ⟨4319225693038832176076935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5758967590718442901435913 4319225693038832176076935)
      ·
        refine ⟨6478838539558248264115403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319225693038832176076935 6478838539558248264115403)
        ·
          refine ⟨9718257809337372396173105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6478838539558248264115403 9718257809337372396173105)
          ·
            refine ⟨7288693357003029297129829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9718257809337372396173105 7288693357003029297129829)
            ·
              refine ⟨1366630004438067993211843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7288693357003029297129829 1366630004438067993211843)
              ·
                refine ⟨2049945006657101989817765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366630004438067993211843 2049945006657101989817765)
                ·
                  refine ⟨384364688748206623090831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049945006657101989817765 384364688748206623090831)
                  ·
                    rfl

theorem cell20_842116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_842116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842116 prefixEnd_842116 := by exact prefixLift 842116
  have htrace : WordTrace (prefixWord ++ tailWord_842116) baseStart_842116 baseEnd_842116 := by
    simpa [prefixWord, tailWord_842116, baseEnd_842116] using wordTrace_append hprefix tailTrace_842116
  have hstable : (prefixWord ++ tailWord_842116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842116).length < 2 ^ (prefixWord ++ tailWord_842116).sum := by decide
  have hdescent : baseEnd_842116 < baseStart_842116 := by decide
  rcases family_descends (prefixWord ++ tailWord_842116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842137 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_842137 : Nat := 118140960795 + 842137 * 2 ^ 59
def prefixEnd_842137 : Nat := 4983230072969 + 3 ^ 40 * 842137 * 2
def baseEnd_842137 : Nat := 384374273720423883390745

theorem tailTrace_842137 : CollatzResearch.WordTrace tailWord_842137 prefixEnd_842137 384374273720423883390745 := by
  unfold tailWord_842137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30715259750088949394172665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20476839833392632929448443 30715259750088949394172665)
  ·
    refine ⟨23036444812566712045629499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30715259750088949394172665 23036444812566712045629499)
    ·
      refine ⟨34554667218850068068444249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23036444812566712045629499 34554667218850068068444249)
      ·
        refine ⟨25916000414137551051333187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34554667218850068068444249 25916000414137551051333187)
        ·
          refine ⟨38874000621206326576999781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25916000414137551051333187 38874000621206326576999781)
          ·
            refine ⟨7288875116476186233187459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38874000621206326576999781 7288875116476186233187459)
            ·
              refine ⟨10933312674714279349781189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7288875116476186233187459 10933312674714279349781189)
              ·
                refine ⟨2049996126508927378083973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10933312674714279349781189 2049996126508927378083973)
                ·
                  refine ⟨384374273720423883390745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2049996126508927378083973 384374273720423883390745)
                  ·
                    rfl

theorem cell20_842137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_842137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842137 prefixEnd_842137 := by exact prefixLift 842137
  have htrace : WordTrace (prefixWord ++ tailWord_842137) baseStart_842137 baseEnd_842137 := by
    simpa [prefixWord, tailWord_842137, baseEnd_842137] using wordTrace_append hprefix tailTrace_842137
  have hstable : (prefixWord ++ tailWord_842137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842137).length < 2 ^ (prefixWord ++ tailWord_842137).sum := by decide
  have hdescent : baseEnd_842137 < baseStart_842137 := by decide
  rcases family_descends (prefixWord ++ tailWord_842137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842157 : List Nat := [1, 5, 2, 2, 3, 1, 6]
def baseStart_842157 : Nat := 118140960795 + 842157 * 2 ^ 59
def prefixEnd_842157 : Nat := 4983230072969 + 3 ^ 40 * 842157 * 2
def baseEnd_842157 : Nat := 42709266918376966969333

theorem tailTrace_842157 : CollatzResearch.WordTrace tailWord_842157 prefixEnd_842157 42709266918376966969333 := by
  unfold tailWord_842157
  simp only [CollatzResearch.WordTrace]
  refine ⟨30715989210016492809900725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20477326140010995206600483 30715989210016492809900725)
  ·
    refine ⟨2879623988439046200928193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30715989210016492809900725 2879623988439046200928193)
    ·
      refine ⟨2159717991329284650696145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2879623988439046200928193 2159717991329284650696145)
      ·
        refine ⟨1619788493496963488022109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2159717991329284650696145 1619788493496963488022109)
        ·
          refine ⟨607420685061361308008291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1619788493496963488022109 607420685061361308008291)
          ·
            refine ⟨911131027592041962012437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607420685061361308008291 911131027592041962012437)
            ·
              refine ⟨42709266918376966969333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 911131027592041962012437 42709266918376966969333)
              ·
                rfl

theorem cell20_842157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 6].length) (baseStart_842157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842157 prefixEnd_842157 := by exact prefixLift 842157
  have htrace : WordTrace (prefixWord ++ tailWord_842157) baseStart_842157 baseEnd_842157 := by
    simpa [prefixWord, tailWord_842157, baseEnd_842157] using wordTrace_append hprefix tailTrace_842157
  have hstable : (prefixWord ++ tailWord_842157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842157).length < 2 ^ (prefixWord ++ tailWord_842157).sum := by decide
  have hdescent : baseEnd_842157 < baseStart_842157 := by decide
  rcases family_descends (prefixWord ++ tailWord_842157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842161 : List Nat := [1, 2, 2, 4, 1, 4, 6]
def baseStart_842161 : Nat := 118140960795 + 842161 * 2 ^ 59
def prefixEnd_842161 : Nat := 4983230072969 + 3 ^ 40 * 842161 * 2
def baseEnd_842161 : Nat := 42709469774931829621183

theorem tailTrace_842161 : CollatzResearch.WordTrace tailWord_842161 prefixEnd_842161 42709469774931829621183 := by
  unfold tailWord_842161
  simp only [CollatzResearch.WordTrace]
  refine ⟨30716135102002001493046337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20477423401334667662030891 30716135102002001493046337)
  ·
    refine ⟨23037101326501501119784753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30716135102002001493046337 23037101326501501119784753)
    ·
      refine ⟨17277825994876125839838565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23037101326501501119784753 17277825994876125839838565)
      ·
        refine ⟨3239592374039273594969731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17277825994876125839838565 3239592374039273594969731)
        ·
          refine ⟨4859388561058910392454597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3239592374039273594969731 4859388561058910392454597)
          ·
            refine ⟨911135355198545698585237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4859388561058910392454597 911135355198545698585237)
            ·
              refine ⟨42709469774931829621183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 911135355198545698585237 42709469774931829621183)
              ·
                rfl

theorem cell20_842161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 6].length) (baseStart_842161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842161 prefixEnd_842161 := by exact prefixLift 842161
  have htrace : WordTrace (prefixWord ++ tailWord_842161) baseStart_842161 baseEnd_842161 := by
    simpa [prefixWord, tailWord_842161, baseEnd_842161] using wordTrace_append hprefix tailTrace_842161
  have hstable : (prefixWord ++ tailWord_842161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842161).length < 2 ^ (prefixWord ++ tailWord_842161).sum := by decide
  have hdescent : baseEnd_842161 < baseStart_842161 := by decide
  rcases family_descends (prefixWord ++ tailWord_842161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842168 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_842168 : Nat := 118140960795 + 842168 * 2 ^ 59
def prefixEnd_842168 : Nat := 4983230072969 + 3 ^ 40 * 842168 * 2
def baseEnd_842168 : Nat := 384388422965125553357285

theorem tailTrace_842168 : CollatzResearch.WordTrace tailWord_842168 prefixEnd_842168 384388422965125553357285 := by
  unfold tailWord_842168
  simp only [CollatzResearch.WordTrace]
  refine ⟨15358195206488320844275579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20477593608651094459034105 15358195206488320844275579)
  ·
    refine ⟨23037292809732481266413369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15358195206488320844275579 23037292809732481266413369)
    ·
      refine ⟨17277969607299360949810027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23037292809732481266413369 17277969607299360949810027)
      ·
        refine ⟨25916954410949041424715041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17277969607299360949810027 25916954410949041424715041)
        ·
          refine ⟨19437715808211781068536281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25916954410949041424715041 19437715808211781068536281)
          ·
            refine ⟨14578286856158835801402211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19437715808211781068536281 14578286856158835801402211)
            ·
              refine ⟨21867430284238253702103317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14578286856158835801402211 21867430284238253702103317)
              ·
                refine ⟨1025035794573668142286093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21867430284238253702103317 1025035794573668142286093)
                ·
                  refine ⟨384388422965125553357285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025035794573668142286093 384388422965125553357285)
                  ·
                    rfl

theorem cell20_842168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_842168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842168 prefixEnd_842168 := by exact prefixLift 842168
  have htrace : WordTrace (prefixWord ++ tailWord_842168) baseStart_842168 baseEnd_842168 := by
    simpa [prefixWord, tailWord_842168, baseEnd_842168] using wordTrace_append hprefix tailTrace_842168
  have hstable : (prefixWord ++ tailWord_842168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842168).length < 2 ^ (prefixWord ++ tailWord_842168).sum := by decide
  have hdescent : baseEnd_842168 < baseStart_842168 := by decide
  rcases family_descends (prefixWord ++ tailWord_842168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842177 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 3]
def baseStart_842177 : Nat := 118140960795 + 842177 * 2 ^ 59
def prefixEnd_842177 : Nat := 4983230072969 + 3 ^ 40 * 842177 * 2
def baseEnd_842177 : Nat := 384392530810361522057249

theorem tailTrace_842177 : CollatzResearch.WordTrace tailWord_842177 prefixEnd_842177 384392530810361522057249 := by
  unfold tailWord_842177
  simp only [CollatzResearch.WordTrace]
  refine ⟨30716718669944036225628785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20477812446629357483752523 30716718669944036225628785)
  ·
    refine ⟨23037539002458027169221589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30716718669944036225628785 23037539002458027169221589)
    ·
      refine ⟨539942320370110011778631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23037539002458027169221589 539942320370110011778631)
      ·
        refine ⟨809913480555165017667947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539942320370110011778631 809913480555165017667947)
        ·
          refine ⟨1214870220832747526501921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 809913480555165017667947 1214870220832747526501921)
          ·
            refine ⟨911152665624560644876441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1214870220832747526501921 911152665624560644876441)
            ·
              refine ⟨683364499218420483657331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911152665624560644876441 683364499218420483657331)
              ·
                refine ⟨1025046748827630725485997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683364499218420483657331 1025046748827630725485997)
                ·
                  refine ⟨384392530810361522057249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025046748827630725485997 384392530810361522057249)
                  ·
                    rfl

theorem cell20_842177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_842177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842177 prefixEnd_842177 := by exact prefixLift 842177
  have htrace : WordTrace (prefixWord ++ tailWord_842177) baseStart_842177 baseEnd_842177 := by
    simpa [prefixWord, tailWord_842177, baseEnd_842177] using wordTrace_append hprefix tailTrace_842177
  have hstable : (prefixWord ++ tailWord_842177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842177).length < 2 ^ (prefixWord ++ tailWord_842177).sum := by decide
  have hdescent : baseEnd_842177 < baseStart_842177 := by decide
  rcases family_descends (prefixWord ++ tailWord_842177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842185 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 3]
def baseStart_842185 : Nat := 118140960795 + 842185 * 2 ^ 59
def prefixEnd_842185 : Nat := 4983230072969 + 3 ^ 40 * 842185 * 2
def baseEnd_842185 : Nat := 384396182228349049790549

theorem tailTrace_842185 : CollatzResearch.WordTrace tailWord_842185 prefixEnd_842185 384396182228349049790549 := by
  unfold tailWord_842185
  simp only [CollatzResearch.WordTrace]
  refine ⟨30717010453915053591920009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20478006969276702394613339 30717010453915053591920009)
  ·
    refine ⟨23037757840436290193940007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30717010453915053591920009 23037757840436290193940007)
    ·
      refine ⟨34556636760654435290910011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23037757840436290193940007 34556636760654435290910011)
      ·
        refine ⟨51834955140981652936365017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34556636760654435290910011 51834955140981652936365017)
        ·
          refine ⟨38876216355736239702273763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51834955140981652936365017 38876216355736239702273763)
          ·
            refine ⟨58314324533604359553410645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38876216355736239702273763 58314324533604359553410645)
            ·
              refine ⟨683370990628176088516531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 58314324533604359553410645 683370990628176088516531)
              ·
                refine ⟨1025056485942264132774797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683370990628176088516531 1025056485942264132774797)
                ·
                  refine ⟨384396182228349049790549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025056485942264132774797 384396182228349049790549)
                  ·
                    rfl

theorem cell20_842185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_842185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842185 prefixEnd_842185 := by exact prefixLift 842185
  have htrace : WordTrace (prefixWord ++ tailWord_842185) baseStart_842185 baseEnd_842185 := by
    simpa [prefixWord, tailWord_842185, baseEnd_842185] using wordTrace_append hprefix tailTrace_842185
  have hstable : (prefixWord ++ tailWord_842185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842185).length < 2 ^ (prefixWord ++ tailWord_842185).sum := by decide
  have hdescent : baseEnd_842185 < baseStart_842185 := by decide
  rcases family_descends (prefixWord ++ tailWord_842185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842226 : List Nat := [3, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_842226 : Nat := 118140960795 + 842226 * 2 ^ 59
def prefixEnd_842226 : Nat := 4983230072969 + 3 ^ 40 * 842226 * 2
def baseEnd_842226 : Nat := 384414895745535129423715

theorem tailTrace_842226 : CollatzResearch.WordTrace tailWord_842226 prefixEnd_842226 384414895745535129423715 := by
  unfold tailWord_842226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7679626461691629398540633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20479003897844345062775021 7679626461691629398540633)
  ·
    refine ⟨5759719846268722048905475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7679626461691629398540633 5759719846268722048905475)
    ·
      refine ⟨8639579769403083073358213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5759719846268722048905475 8639579769403083073358213)
      ·
        refine ⟨1619921206763078076254665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8639579769403083073358213 1619921206763078076254665)
        ·
          refine ⟨1214940905072308557190999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1619921206763078076254665 1214940905072308557190999)
          ·
            refine ⟨1822411357608462835786499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1214940905072308557190999 1822411357608462835786499)
            ·
              refine ⟨2733617036412694253679749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822411357608462835786499 2733617036412694253679749)
              ·
                refine ⟨512553194327380172564953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2733617036412694253679749 512553194327380172564953)
                ·
                  refine ⟨384414895745535129423715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512553194327380172564953 384414895745535129423715)
                  ·
                    rfl

theorem cell20_842226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_842226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842226 prefixEnd_842226 := by exact prefixLift 842226
  have htrace : WordTrace (prefixWord ++ tailWord_842226) baseStart_842226 baseEnd_842226 := by
    simpa [prefixWord, tailWord_842226, baseEnd_842226] using wordTrace_append hprefix tailTrace_842226
  have hstable : (prefixWord ++ tailWord_842226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842226).length < 2 ^ (prefixWord ++ tailWord_842226).sum := by decide
  have hdescent : baseEnd_842226 < baseStart_842226 := by decide
  rcases family_descends (prefixWord ++ tailWord_842226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842230 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_842230 : Nat := 118140960795 + 842230 * 2 ^ 59
def prefixEnd_842230 : Nat := 4983230072969 + 3 ^ 40 * 842230 * 2
def baseEnd_842230 : Nat := 384416721454528893290365

theorem tailTrace_842230 : CollatzResearch.WordTrace tailWord_842230 prefixEnd_842230 384416721454528893290365 := by
  unfold tailWord_842230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1919915733672001642331759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20479101159168017518205429 1919915733672001642331759)
  ·
    refine ⟨2879873600508002463497639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1919915733672001642331759 2879873600508002463497639)
    ·
      refine ⟨4319810400762003695246459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2879873600508002463497639 4319810400762003695246459)
      ·
        refine ⟨6479715601143005542869689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319810400762003695246459 6479715601143005542869689)
        ·
          refine ⟨4859786700857254157152267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6479715601143005542869689 4859786700857254157152267)
          ·
            refine ⟨7289680051285881235728401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4859786700857254157152267 7289680051285881235728401)
            ·
              refine ⟨5467260038464410926796301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289680051285881235728401 5467260038464410926796301)
              ·
                refine ⟨2050222514424154097548613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5467260038464410926796301 2050222514424154097548613)
                ·
                  refine ⟨384416721454528893290365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050222514424154097548613 384416721454528893290365)
                  ·
                    rfl

theorem cell20_842230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_842230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842230 prefixEnd_842230 := by exact prefixLift 842230
  have htrace : WordTrace (prefixWord ++ tailWord_842230) baseStart_842230 baseEnd_842230 := by
    simpa [prefixWord, tailWord_842230, baseEnd_842230] using wordTrace_append hprefix tailTrace_842230
  have hstable : (prefixWord ++ tailWord_842230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842230).length < 2 ^ (prefixWord ++ tailWord_842230).sum := by decide
  have hdescent : baseEnd_842230 < baseStart_842230 := by decide
  rcases family_descends (prefixWord ++ tailWord_842230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842251 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_842251 : Nat := 118140960795 + 842251 * 2 ^ 59
def prefixEnd_842251 : Nat := 4983230072969 + 3 ^ 40 * 842251 * 2
def baseEnd_842251 : Nat := 384426306426746153590279

theorem tailTrace_842251 : CollatzResearch.WordTrace tailWord_842251 prefixEnd_842251 384426306426746153590279 := by
  unfold tailWord_842251
  simp only [CollatzResearch.WordTrace]
  refine ⟨30719417671675946863822607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20479611781117297909215071 30719417671675946863822607)
  ·
    refine ⟨46079126507513920295733911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30719417671675946863822607 46079126507513920295733911)
    ·
      refine ⟨69118689761270880443600867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46079126507513920295733911 69118689761270880443600867)
      ·
        refine ⟨103678034641906320665401301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69118689761270880443600867 103678034641906320665401301)
        ·
          refine ⟨2429953936919679390595343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 103678034641906320665401301 2429953936919679390595343)
          ·
            refine ⟨3644930905379519085893015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429953936919679390595343 3644930905379519085893015)
            ·
              refine ⟨5467396358069278628839523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644930905379519085893015 5467396358069278628839523)
              ·
                refine ⟨8201094537103917943259285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467396358069278628839523 8201094537103917943259285)
                ·
                  refine ⟨384426306426746153590279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8201094537103917943259285 384426306426746153590279)
                  ·
                    rfl

theorem cell20_842251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_842251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842251 prefixEnd_842251 := by exact prefixLift 842251
  have htrace : WordTrace (prefixWord ++ tailWord_842251) baseStart_842251 baseEnd_842251 := by
    simpa [prefixWord, tailWord_842251, baseEnd_842251] using wordTrace_append hprefix tailTrace_842251
  have hstable : (prefixWord ++ tailWord_842251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842251).length < 2 ^ (prefixWord ++ tailWord_842251).sum := by decide
  have hdescent : baseEnd_842251 < baseStart_842251 := by decide
  rcases family_descends (prefixWord ++ tailWord_842251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842254 : List Nat := [4, 1, 1, 2, 3, 2, 3, 4]
def baseStart_842254 : Nat := 118140960795 + 842254 * 2 ^ 59
def prefixEnd_842254 : Nat := 4983230072969 + 3 ^ 40 * 842254 * 2
def baseEnd_842254 : Nat := 128142558569497158830089

theorem tailTrace_842254 : CollatzResearch.WordTrace tailWord_842254 prefixEnd_842254 128142558569497158830089 := by
  unfold tailWord_842254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3839940886333134797022727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20479684727110052250787877 3839940886333134797022727)
  ·
    refine ⟨5759911329499702195534091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3839940886333134797022727 5759911329499702195534091)
    ·
      refine ⟨8639866994249553293301137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5759911329499702195534091 8639866994249553293301137)
      ·
        refine ⟨6479900245687164969975853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8639866994249553293301137 6479900245687164969975853)
        ·
          refine ⟨2429962592132686863740945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6479900245687164969975853 2429962592132686863740945)
          ·
            refine ⟨1822471944099515147805709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2429962592132686863740945 1822471944099515147805709)
            ·
              refine ⟨683426979037318180427141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1822471944099515147805709 683426979037318180427141)
              ·
                refine ⟨128142558569497158830089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 683426979037318180427141 128142558569497158830089)
                ·
                  rfl

theorem cell20_842254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_842254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842254 prefixEnd_842254 := by exact prefixLift 842254
  have htrace : WordTrace (prefixWord ++ tailWord_842254) baseStart_842254 baseEnd_842254 := by
    simpa [prefixWord, tailWord_842254, baseEnd_842254] using wordTrace_append hprefix tailTrace_842254
  have hstable : (prefixWord ++ tailWord_842254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842254).length < 2 ^ (prefixWord ++ tailWord_842254).sum := by decide
  have hdescent : baseEnd_842254 < baseStart_842254 := by decide
  rcases family_descends (prefixWord ++ tailWord_842254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842265 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 7]
def baseStart_842265 : Nat := 118140960795 + 842265 * 2 ^ 59
def prefixEnd_842265 : Nat := 4983230072969 + 3 ^ 40 * 842265 * 2
def baseEnd_842265 : Nat := 384432696408224327123555

theorem tailTrace_842265 : CollatzResearch.WordTrace tailWord_842265 prefixEnd_842265 384432696408224327123555 := by
  unfold tailWord_842265
  simp only [CollatzResearch.WordTrace]
  refine ⟨30719928293625227254832249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20479952195750151503221499 30719928293625227254832249)
  ·
    refine ⟨23039946220218920441124187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30719928293625227254832249 23039946220218920441124187)
    ·
      refine ⟨34559919330328380661686281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23039946220218920441124187 34559919330328380661686281)
      ·
        refine ⟨25919939497746285496264711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34559919330328380661686281 25919939497746285496264711)
        ·
          refine ⟨38879909246619428244397067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25919939497746285496264711 38879909246619428244397067)
          ·
            refine ⟨58319863869929142366595601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38879909246619428244397067 58319863869929142366595601)
            ·
              refine ⟨43739897902446856774946701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58319863869929142366595601 43739897902446856774946701)
              ·
                refine ⟨16402461713417571290605013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43739897902446856774946701 16402461713417571290605013)
                ·
                  refine ⟨384432696408224327123555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16402461713417571290605013 384432696408224327123555)
                  ·
                    rfl

theorem cell20_842265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_842265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842265 prefixEnd_842265 := by exact prefixLift 842265
  have htrace : WordTrace (prefixWord ++ tailWord_842265) baseStart_842265 baseEnd_842265 := by
    simpa [prefixWord, tailWord_842265, baseEnd_842265] using wordTrace_append hprefix tailTrace_842265
  have hstable : (prefixWord ++ tailWord_842265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842265).length < 2 ^ (prefixWord ++ tailWord_842265).sum := by decide
  have hdescent : baseEnd_842265 < baseStart_842265 := by decide
  rcases family_descends (prefixWord ++ tailWord_842265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842289 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 4]
def baseStart_842289 : Nat := 118140960795 + 842289 * 2 ^ 59
def prefixEnd_842289 : Nat := 4983230072969 + 3 ^ 40 * 842289 * 2
def baseEnd_842289 : Nat := 384443650662186910323457

theorem tailTrace_842289 : CollatzResearch.WordTrace tailWord_842289 prefixEnd_842289 384443650662186910323457 := by
  unfold tailWord_842289
  simp only [CollatzResearch.WordTrace]
  refine ⟨30720803645538279353705921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20480535763692186235803947 30720803645538279353705921)
  ·
    refine ⟨23040602734153709515279441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30720803645538279353705921 23040602734153709515279441)
    ·
      refine ⟨17280452050615282136459581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23040602734153709515279441 17280452050615282136459581)
      ·
        refine ⟨6480169518980730801172343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17280452050615282136459581 6480169518980730801172343)
        ·
          refine ⟨9720254278471096201758515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6480169518980730801172343 9720254278471096201758515)
          ·
            refine ⟨14580381417706644302637773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9720254278471096201758515 14580381417706644302637773)
            ·
              refine ⟨5467643031639991613489165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14580381417706644302637773 5467643031639991613489165)
              ·
                refine ⟨2050366136864996855058437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5467643031639991613489165 2050366136864996855058437)
                ·
                  refine ⟨384443650662186910323457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050366136864996855058437 384443650662186910323457)
                  ·
                    rfl

theorem cell20_842289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_842289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842289 prefixEnd_842289 := by exact prefixLift 842289
  have htrace : WordTrace (prefixWord ++ tailWord_842289) baseStart_842289 baseEnd_842289 := by
    simpa [prefixWord, tailWord_842289, baseEnd_842289] using wordTrace_append hprefix tailTrace_842289
  have hstable : (prefixWord ++ tailWord_842289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842289).length < 2 ^ (prefixWord ++ tailWord_842289).sum := by decide
  have hdescent : baseEnd_842289 < baseStart_842289 := by decide
  rcases family_descends (prefixWord ++ tailWord_842289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842296 : List Nat := [2, 1, 2, 1, 4, 1, 2, 7]
def baseStart_842296 : Nat := 118140960795 + 842296 * 2 ^ 59
def prefixEnd_842296 : Nat := 4983230072969 + 3 ^ 40 * 842296 * 2
def baseEnd_842296 : Nat := 128148948550975332363365

theorem tailTrace_842296 : CollatzResearch.WordTrace tailWord_842296 prefixEnd_842296 128148948550975332363365 := by
  unfold tailWord_842296
  simp only [CollatzResearch.WordTrace]
  refine ⟨15360529478256459774605371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20480705971008613032807161 15360529478256459774605371)
  ·
    refine ⟨23040794217384689661908057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15360529478256459774605371 23040794217384689661908057)
    ·
      refine ⟨17280595663038517246431043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23040794217384689661908057 17280595663038517246431043)
      ·
        refine ⟨25920893494557775869646565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17280595663038517246431043 25920893494557775869646565)
        ·
          refine ⟨4860167530229582975558731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25920893494557775869646565 4860167530229582975558731)
          ·
            refine ⟨7290251295344374463338097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860167530229582975558731 7290251295344374463338097)
            ·
              refine ⟨5467688471508280847503573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7290251295344374463338097 5467688471508280847503573)
              ·
                refine ⟨128148948550975332363365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5467688471508280847503573 128148948550975332363365)
                ·
                  rfl

theorem cell20_842296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_842296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842296 prefixEnd_842296 := by exact prefixLift 842296
  have htrace : WordTrace (prefixWord ++ tailWord_842296) baseStart_842296 baseEnd_842296 := by
    simpa [prefixWord, tailWord_842296, baseEnd_842296] using wordTrace_append hprefix tailTrace_842296
  have hstable : (prefixWord ++ tailWord_842296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842296).length < 2 ^ (prefixWord ++ tailWord_842296).sum := by decide
  have hdescent : baseEnd_842296 < baseStart_842296 := by decide
  rcases family_descends (prefixWord ++ tailWord_842296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842379 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 5]
def baseStart_842379 : Nat := 118140960795 + 842379 * 2 ^ 59
def prefixEnd_842379 : Nat := 4983230072969 + 3 ^ 40 * 842379 * 2
def baseEnd_842379 : Nat := 384484729114546597323089

theorem tailTrace_842379 : CollatzResearch.WordTrace tailWord_842379 prefixEnd_842379 384484729114546597323089 := by
  unfold tailWord_842379
  simp only [CollatzResearch.WordTrace]
  refine ⟨30724086215212224724482191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20482724143474816482988127 30724086215212224724482191)
  ·
    refine ⟨46086129322818337086723287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30724086215212224724482191 46086129322818337086723287)
    ·
      refine ⟨69129193984227505630084931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46086129322818337086723287 69129193984227505630084931)
      ·
        refine ⟨103693790976341258445127397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69129193984227505630084931 103693790976341258445127397)
        ·
          refine ⟨19442585808063985958461387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103693790976341258445127397 19442585808063985958461387)
          ·
            refine ⟨29163878712095978937692081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19442585808063985958461387 29163878712095978937692081)
            ·
              refine ⟨21872909034071984203269061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29163878712095978937692081 21872909034071984203269061)
              ·
                refine ⟨4101170443888497038112949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21872909034071984203269061 4101170443888497038112949)
                ·
                  refine ⟨384484729114546597323089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4101170443888497038112949 384484729114546597323089)
                  ·
                    rfl

theorem cell20_842379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_842379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842379 prefixEnd_842379 := by exact prefixLift 842379
  have htrace : WordTrace (prefixWord ++ tailWord_842379) baseStart_842379 baseEnd_842379 := by
    simpa [prefixWord, tailWord_842379, baseEnd_842379] using wordTrace_append hprefix tailTrace_842379
  have hstable : (prefixWord ++ tailWord_842379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842379).length < 2 ^ (prefixWord ++ tailWord_842379).sum := by decide
  have hdescent : baseEnd_842379 < baseStart_842379 := by decide
  rcases family_descends (prefixWord ++ tailWord_842379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842413 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 3]
def baseStart_842413 : Nat := 118140960795 + 842413 * 2 ^ 59
def prefixEnd_842413 : Nat := 4983230072969 + 3 ^ 40 * 842413 * 2
def baseEnd_842413 : Nat := 384500247640993590189617

theorem tailTrace_842413 : CollatzResearch.WordTrace tailWord_842413 prefixEnd_842413 384500247640993590189617 := by
  unfold tailWord_842413
  simp only [CollatzResearch.WordTrace]
  refine ⟨30725326297089048531219893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20483550864726032354146595 30725326297089048531219893)
  ·
    refine ⟨2880499340352098299801865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30725326297089048531219893 2880499340352098299801865)
    ·
      refine ⟨2160374505264073724851399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2880499340352098299801865 2160374505264073724851399)
      ·
        refine ⟨3240561757896110587277099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160374505264073724851399 3240561757896110587277099)
        ·
          refine ⟨4860842636844165880915649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240561757896110587277099 4860842636844165880915649)
          ·
            refine ⟨3645631977633124410686737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4860842636844165880915649 3645631977633124410686737)
            ·
              refine ⟨2734223983224843308015053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645631977633124410686737 2734223983224843308015053)
              ·
                refine ⟨1025333993709316240505645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2734223983224843308015053 1025333993709316240505645)
                ·
                  refine ⟨384500247640993590189617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025333993709316240505645 384500247640993590189617)
                  ·
                    rfl

theorem cell20_842413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_842413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842413 prefixEnd_842413 := by exact prefixLift 842413
  have htrace : WordTrace (prefixWord ++ tailWord_842413) baseStart_842413 baseEnd_842413 := by
    simpa [prefixWord, tailWord_842413, baseEnd_842413] using wordTrace_append hprefix tailTrace_842413
  have hstable : (prefixWord ++ tailWord_842413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842413).length < 2 ^ (prefixWord ++ tailWord_842413).sum := by decide
  have hdescent : baseEnd_842413 < baseStart_842413 := by decide
  rcases family_descends (prefixWord ++ tailWord_842413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842433 : List Nat := [1, 2, 6, 2, 1, 1, 2, 3, 2]
def baseStart_842433 : Nat := 118140960795 + 842433 * 2 ^ 59
def prefixEnd_842433 : Nat := 4983230072969 + 3 ^ 40 * 842433 * 2
def baseEnd_842433 : Nat := 384509376185962409522869

theorem tailTrace_842433 : CollatzResearch.WordTrace tailWord_842433 prefixEnd_842433 384509376185962409522869 := by
  unfold tailWord_842433
  simp only [CollatzResearch.WordTrace]
  refine ⟨30726055757016591946947953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20484037171344394631298635 30726055757016591946947953)
  ·
    refine ⟨23044541817762443960210965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30726055757016591946947953 23044541817762443960210965)
    ·
      refine ⟨1080212897707614560634889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23044541817762443960210965 1080212897707614560634889)
      ·
        refine ⟨810159673280710920476167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1080212897707614560634889 810159673280710920476167)
        ·
          refine ⟨1215239509921066380714251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810159673280710920476167 1215239509921066380714251)
          ·
            refine ⟨1822859264881599571071377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215239509921066380714251 1822859264881599571071377)
            ·
              refine ⟨1367144448661199678303533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1822859264881599571071377 1367144448661199678303533)
              ·
                refine ⟨512679168247949879363825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1367144448661199678303533 512679168247949879363825)
                ·
                  refine ⟨384509376185962409522869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512679168247949879363825 384509376185962409522869)
                  ·
                    rfl

theorem cell20_842433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_842433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842433 prefixEnd_842433 := by exact prefixLift 842433
  have htrace : WordTrace (prefixWord ++ tailWord_842433) baseStart_842433 baseEnd_842433 := by
    simpa [prefixWord, tailWord_842433, baseEnd_842433] using wordTrace_append hprefix tailTrace_842433
  have hstable : (prefixWord ++ tailWord_842433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842433).length < 2 ^ (prefixWord ++ tailWord_842433).sum := by decide
  have hdescent : baseEnd_842433 < baseStart_842433 := by decide
  rcases family_descends (prefixWord ++ tailWord_842433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842458 : List Nat := [3, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_842458 : Nat := 118140960795 + 842458 * 2 ^ 59
def prefixEnd_842458 : Nat := 4983230072969 + 3 ^ 40 * 842458 * 2
def baseEnd_842458 : Nat := 384520786867173433689433

theorem tailTrace_842458 : CollatzResearch.WordTrace tailWord_842458 prefixEnd_842458 384520786867173433689433 := by
  unfold tailWord_842458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7681741895481505304152007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20484645054617347477738685 7681741895481505304152007)
  ·
    refine ⟨11522612843222257956228011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7681741895481505304152007 11522612843222257956228011)
    ·
      refine ⟨17283919264833386934342017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11522612843222257956228011 17283919264833386934342017)
      ·
        refine ⟨12962939448625040200756513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17283919264833386934342017 12962939448625040200756513)
        ·
          refine ⟨9722204586468780150567385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12962939448625040200756513 9722204586468780150567385)
          ·
            refine ⟨7291653439851585112925539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9722204586468780150567385 7291653439851585112925539)
            ·
              refine ⟨10937480159777377669388309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291653439851585112925539 10937480159777377669388309)
              ·
                refine ⟨512694382489564578252577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10937480159777377669388309 512694382489564578252577)
                ·
                  refine ⟨384520786867173433689433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512694382489564578252577 384520786867173433689433)
                  ·
                    rfl

theorem cell20_842458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_842458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842458 prefixEnd_842458 := by exact prefixLift 842458
  have htrace : WordTrace (prefixWord ++ tailWord_842458) baseStart_842458 baseEnd_842458 := by
    simpa [prefixWord, tailWord_842458, baseEnd_842458] using wordTrace_append hprefix tailTrace_842458
  have hstable : (prefixWord ++ tailWord_842458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842458).length < 2 ^ (prefixWord ++ tailWord_842458).sum := by decide
  have hdescent : baseEnd_842458 < baseStart_842458 := by decide
  rcases family_descends (prefixWord ++ tailWord_842458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842479 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_842479 : Nat := 118140960795 + 842479 * 2 ^ 59
def prefixEnd_842479 : Nat := 4983230072969 + 3 ^ 40 * 842479 * 2
def baseEnd_842479 : Nat := 384530371839390693989347

theorem tailTrace_842479 : CollatzResearch.WordTrace tailWord_842479 prefixEnd_842479 384530371839390693989347 := by
  unfold tailWord_842479
  simp only [CollatzResearch.WordTrace]
  refine ⟨30727733514849941803122491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20485155676566627868748327 30727733514849941803122491)
  ·
    refine ⟨46091600272274912704683737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30727733514849941803122491 46091600272274912704683737)
    ·
      refine ⟨34568700204206184528512803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46091600272274912704683737 34568700204206184528512803)
      ·
        refine ⟨51853050306309276792769205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34568700204206184528512803 51853050306309276792769205)
        ·
          refine ⟨4861223466216494699322113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51853050306309276792769205 4861223466216494699322113)
          ·
            refine ⟨3645917599662371024491585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4861223466216494699322113 3645917599662371024491585)
            ·
              refine ⟨2734438199746778268368689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645917599662371024491585 2734438199746778268368689)
              ·
                refine ⟨2050828649810083701276517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2734438199746778268368689 2050828649810083701276517)
                ·
                  refine ⟨384530371839390693989347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2050828649810083701276517 384530371839390693989347)
                  ·
                    rfl

theorem cell20_842479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_842479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842479 prefixEnd_842479 := by exact prefixLift 842479
  have htrace : WordTrace (prefixWord ++ tailWord_842479) baseStart_842479 baseEnd_842479 := by
    simpa [prefixWord, tailWord_842479, baseEnd_842479] using wordTrace_append hprefix tailTrace_842479
  have hstable : (prefixWord ++ tailWord_842479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842479).length < 2 ^ (prefixWord ++ tailWord_842479).sum := by decide
  have hdescent : baseEnd_842479 < baseStart_842479 := by decide
  rcases family_descends (prefixWord ++ tailWord_842479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842482 : List Nat := [3, 2, 1, 3, 1, 4, 2, 4]
def baseStart_842482 : Nat := 118140960795 + 842482 * 2 ^ 59
def prefixEnd_842482 : Nat := 4983230072969 + 3 ^ 40 * 842482 * 2
def baseEnd_842482 : Nat := 128177247040378672296445

theorem tailTrace_842482 : CollatzResearch.WordTrace tailWord_842482 prefixEnd_842482 128177247040378672296445 := by
  unfold tailWord_842482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7681960733459768328870425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20485228622559382210321133 7681960733459768328870425)
  ·
    refine ⟨5761470550094826246652819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7681960733459768328870425 5761470550094826246652819)
    ·
      refine ⟨8642205825142239369979229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5761470550094826246652819 8642205825142239369979229)
      ·
        refine ⟨3240827184428339763742211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8642205825142239369979229 3240827184428339763742211)
        ·
          refine ⟨4861240776642509645613317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240827184428339763742211 4861240776642509645613317)
          ·
            refine ⟨911482645620470558552497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4861240776642509645613317 911482645620470558552497)
            ·
              refine ⟨683611984215352918914373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911482645620470558552497 683611984215352918914373)
              ·
                refine ⟨128177247040378672296445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 683611984215352918914373 128177247040378672296445)
                ·
                  rfl

theorem cell20_842482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_842482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842482 prefixEnd_842482 := by exact prefixLift 842482
  have htrace : WordTrace (prefixWord ++ tailWord_842482) baseStart_842482 baseEnd_842482 := by
    simpa [prefixWord, tailWord_842482, baseEnd_842482] using wordTrace_append hprefix tailTrace_842482
  have hstable : (prefixWord ++ tailWord_842482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842482).length < 2 ^ (prefixWord ++ tailWord_842482).sum := by decide
  have hdescent : baseEnd_842482 < baseStart_842482 := by decide
  rcases family_descends (prefixWord ++ tailWord_842482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842493 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_842493 : Nat := 118140960795 + 842493 * 2 ^ 59
def prefixEnd_842493 : Nat := 4983230072969 + 3 ^ 40 * 842493 * 2
def baseEnd_842493 : Nat := 384536761820868867522623

theorem tailTrace_842493 : CollatzResearch.WordTrace tailWord_842493 prefixEnd_842493 384536761820868867522623 := by
  unfold tailWord_842493
  simp only [CollatzResearch.WordTrace]
  refine ⟨30728244136799222194132133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20485496091199481462754755 30728244136799222194132133)
  ·
    refine ⟨5761545775649854161399775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30728244136799222194132133 5761545775649854161399775)
    ·
      refine ⟨8642318663474781242099663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5761545775649854161399775 8642318663474781242099663)
      ·
        refine ⟨12963477995212171863149495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8642318663474781242099663 12963477995212171863149495)
        ·
          refine ⟨19445216992818257794724243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12963477995212171863149495 19445216992818257794724243)
          ·
            refine ⟨29167825489227386692086365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19445216992818257794724243 29167825489227386692086365)
            ·
              refine ⟨10937934558460270009532387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29167825489227386692086365 10937934558460270009532387)
              ·
                refine ⟨16406901837690405014298581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10937934558460270009532387 16406901837690405014298581)
                ·
                  refine ⟨384536761820868867522623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16406901837690405014298581 384536761820868867522623)
                  ·
                    rfl

theorem cell20_842493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_842493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842493 prefixEnd_842493 := by exact prefixLift 842493
  have htrace : WordTrace (prefixWord ++ tailWord_842493) baseStart_842493 baseEnd_842493 := by
    simpa [prefixWord, tailWord_842493, baseEnd_842493] using wordTrace_append hprefix tailTrace_842493
  have hstable : (prefixWord ++ tailWord_842493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842493).length < 2 ^ (prefixWord ++ tailWord_842493).sum := by decide
  have hdescent : baseEnd_842493 < baseStart_842493 := by decide
  rcases family_descends (prefixWord ++ tailWord_842493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842503 : List Nat := [1, 1, 4, 4, 1, 3, 6]
def baseStart_842503 : Nat := 118140960795 + 842503 * 2 ^ 59
def prefixEnd_842503 : Nat := 4983230072969 + 3 ^ 40 * 842503 * 2
def baseEnd_842503 : Nat := 42726814010372586354361

theorem tailTrace_842503 : CollatzResearch.WordTrace tailWord_842503 prefixEnd_842503 42726814010372586354361 := by
  unfold tailWord_842503
  simp only [CollatzResearch.WordTrace]
  refine ⟨30728608866762993901996163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20485739244508662601330775 30728608866762993901996163)
  ·
    refine ⟨46092913300144490852994245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30728608866762993901996163 46092913300144490852994245)
    ·
      refine ⟨8642421243777092034936421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46092913300144490852994245 8642421243777092034936421)
      ·
        refine ⟨1620453983208204756550579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8642421243777092034936421 1620453983208204756550579)
        ·
          refine ⟨2430680974812307134825869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1620453983208204756550579 2430680974812307134825869)
          ·
            refine ⟨911505365554615175559701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2430680974812307134825869 911505365554615175559701)
            ·
              refine ⟨42726814010372586354361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 911505365554615175559701 42726814010372586354361)
              ·
                rfl

theorem cell20_842503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 6].length) (baseStart_842503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842503 prefixEnd_842503 := by exact prefixLift 842503
  have htrace : WordTrace (prefixWord ++ tailWord_842503) baseStart_842503 baseEnd_842503 := by
    simpa [prefixWord, tailWord_842503, baseEnd_842503] using wordTrace_append hprefix tailTrace_842503
  have hstable : (prefixWord ++ tailWord_842503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842503).length < 2 ^ (prefixWord ++ tailWord_842503).sum := by decide
  have hdescent : baseEnd_842503 < baseStart_842503 := by decide
  rcases family_descends (prefixWord ++ tailWord_842503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842510 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_842510 : Nat := 118140960795 + 842510 * 2 ^ 59
def prefixEnd_842510 : Nat := 4983230072969 + 3 ^ 40 * 842510 * 2
def baseEnd_842510 : Nat := 384544521084092363955887

theorem tailTrace_842510 : CollatzResearch.WordTrace tailWord_842510 prefixEnd_842510 384544521084092363955887 := by
  unfold tailWord_842510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3841108022217204262187623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20485909451825089398333989 3841108022217204262187623)
  ·
    refine ⟨5761662033325806393281435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3841108022217204262187623 5761662033325806393281435)
    ·
      refine ⟨8642493049988709589922153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5761662033325806393281435 8642493049988709589922153)
      ·
        refine ⟨6481869787491532192441615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8642493049988709589922153 6481869787491532192441615)
        ·
          refine ⟨9722804681237298288662423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6481869787491532192441615 9722804681237298288662423)
          ·
            refine ⟨14584207021855947432993635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9722804681237298288662423 14584207021855947432993635)
            ·
              refine ⟨21876310532783921149490453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14584207021855947432993635 21876310532783921149490453)
              ·
                refine ⟨1025452056224246303882365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21876310532783921149490453 1025452056224246303882365)
                ·
                  refine ⟨384544521084092363955887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025452056224246303882365 384544521084092363955887)
                  ·
                    rfl

theorem cell20_842510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_842510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842510 prefixEnd_842510 := by exact prefixLift 842510
  have htrace : WordTrace (prefixWord ++ tailWord_842510) baseStart_842510 baseEnd_842510 := by
    simpa [prefixWord, tailWord_842510, baseEnd_842510] using wordTrace_append hprefix tailTrace_842510
  have hstable : (prefixWord ++ tailWord_842510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842510).length < 2 ^ (prefixWord ++ tailWord_842510).sum := by decide
  have hdescent : baseEnd_842510 < baseStart_842510 := by decide
  rcases family_descends (prefixWord ++ tailWord_842510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842524 : List Nat := [2, 2, 3, 1, 1, 3, 1, 7]
def baseStart_842524 : Nat := 118140960795 + 842524 * 2 ^ 59
def prefixEnd_842524 : Nat := 4983230072969 + 3 ^ 40 * 842524 * 2
def baseEnd_842524 : Nat := 128183637021856845829721

theorem tailTrace_842524 : CollatzResearch.WordTrace tailWord_842524 prefixEnd_842524 128183637021856845829721 := by
  unfold tailWord_842524
  simp only [CollatzResearch.WordTrace]
  refine ⟨15364687399843457244255313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20486249866457942992340417 15364687399843457244255313)
  ·
    refine ⟨11523515549882592933191485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15364687399843457244255313 11523515549882592933191485)
    ·
      refine ⟨4321318331205972349946807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11523515549882592933191485 4321318331205972349946807)
      ·
        refine ⟨6481977496808958524920211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4321318331205972349946807 6481977496808958524920211)
        ·
          refine ⟨9722966245213437787380317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6481977496808958524920211 9722966245213437787380317)
          ·
            refine ⟨3646112341955039170267619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9722966245213437787380317 3646112341955039170267619)
            ·
              refine ⟨5469168512932558755401429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646112341955039170267619 5469168512932558755401429)
              ·
                refine ⟨128183637021856845829721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5469168512932558755401429 128183637021856845829721)
                ·
                  rfl

theorem cell20_842524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_842524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842524 prefixEnd_842524 := by exact prefixLift 842524
  have htrace : WordTrace (prefixWord ++ tailWord_842524) baseStart_842524 baseEnd_842524 := by
    simpa [prefixWord, tailWord_842524, baseEnd_842524] using wordTrace_append hprefix tailTrace_842524
  have hstable : (prefixWord ++ tailWord_842524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842524).length < 2 ^ (prefixWord ++ tailWord_842524).sum := by decide
  have hdescent : baseEnd_842524 < baseStart_842524 := by decide
  rcases family_descends (prefixWord ++ tailWord_842524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842527 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 3]
def baseStart_842527 : Nat := 118140960795 + 842527 * 2 ^ 59
def prefixEnd_842527 : Nat := 4983230072969 + 3 ^ 40 * 842527 * 2
def baseEnd_842527 : Nat := 384552280347315860389151

theorem tailTrace_842527 : CollatzResearch.WordTrace tailWord_842527 prefixEnd_842527 384552280347315860389151 := by
  unfold tailWord_842527
  simp only [CollatzResearch.WordTrace]
  refine ⟨30729484218676046000869835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20486322812450697333913223 30729484218676046000869835)
  ·
    refine ⟨46094226328014069001304753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30729484218676046000869835 46094226328014069001304753)
    ·
      refine ⟨34570669746010551750978565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46094226328014069001304753 34570669746010551750978565)
      ·
        refine ⟨6482000577376978453308481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34570669746010551750978565 6482000577376978453308481)
        ·
          refine ⟨4861500433032733839981361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6482000577376978453308481 4861500433032733839981361)
          ·
            refine ⟨3646125324774550379986021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4861500433032733839981361 3646125324774550379986021)
            ·
              refine ⟨683648498395228196247379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3646125324774550379986021 683648498395228196247379)
              ·
                refine ⟨1025472747592842294371069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683648498395228196247379 1025472747592842294371069)
                ·
                  refine ⟨384552280347315860389151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025472747592842294371069 384552280347315860389151)
                  ·
                    rfl

theorem cell20_842527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 3].length) (baseStart_842527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842527 prefixEnd_842527 := by exact prefixLift 842527
  have htrace : WordTrace (prefixWord ++ tailWord_842527) baseStart_842527 baseEnd_842527 := by
    simpa [prefixWord, tailWord_842527, baseEnd_842527] using wordTrace_append hprefix tailTrace_842527
  have hstable : (prefixWord ++ tailWord_842527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842527).length < 2 ^ (prefixWord ++ tailWord_842527).sum := by decide
  have hdescent : baseEnd_842527 < baseStart_842527 := by decide
  rcases family_descends (prefixWord ++ tailWord_842527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842564 : List Nat := [2, 3, 4, 2, 1, 2, 2, 2, 2]
def baseStart_842564 : Nat := 118140960795 + 842564 * 2 ^ 59
def prefixEnd_842564 : Nat := 4983230072969 + 3 ^ 40 * 842564 * 2
def baseEnd_842564 : Nat := 384569168155508176155667

theorem tailTrace_842564 : CollatzResearch.WordTrace tailWord_842564 prefixEnd_842564 384569168155508176155667 := by
  unfold tailWord_842564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15365416859771000659983373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20487222479694667546644497 15365416859771000659983373)
  ·
    refine ⟨5762031322414125247493765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15365416859771000659983373 5762031322414125247493765)
    ·
      refine ⟨1080380872952648483905081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5762031322414125247493765 1080380872952648483905081)
      ·
        refine ⟨810285654714486362928811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1080380872952648483905081 810285654714486362928811)
        ·
          refine ⟨1215428482071729544393217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 810285654714486362928811 1215428482071729544393217)
          ·
            refine ⟨911571361553797158294913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215428482071729544393217 911571361553797158294913)
            ·
              refine ⟨683678521165347868721185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911571361553797158294913 683678521165347868721185)
              ·
                refine ⟨512758890874010901540889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683678521165347868721185 512758890874010901540889)
                ·
                  refine ⟨384569168155508176155667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512758890874010901540889 384569168155508176155667)
                  ·
                    rfl

theorem cell20_842564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_842564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842564 prefixEnd_842564 := by exact prefixLift 842564
  have htrace : WordTrace (prefixWord ++ tailWord_842564) baseStart_842564 baseEnd_842564 := by
    simpa [prefixWord, tailWord_842564, baseEnd_842564] using wordTrace_append hprefix tailTrace_842564
  have hstable : (prefixWord ++ tailWord_842564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842564).length < 2 ^ (prefixWord ++ tailWord_842564).sum := by decide
  have hdescent : baseEnd_842564 < baseStart_842564 := by decide
  rcases family_descends (prefixWord ++ tailWord_842564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842586 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_842586 : Nat := 118140960795 + 842586 * 2 ^ 59
def prefixEnd_842586 : Nat := 4983230072969 + 3 ^ 40 * 842586 * 2
def baseEnd_842586 : Nat := 384579209554973877422243

theorem tailTrace_842586 : CollatzResearch.WordTrace tailWord_842586 prefixEnd_842586 384579209554973877422243 := by
  unfold tailWord_842586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682909031365574769316903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20487757416974866051511741 7682909031365574769316903)
  ·
    refine ⟨11524363547048362153975355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7682909031365574769316903 11524363547048362153975355)
    ·
      refine ⟨17286545320572543230963033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11524363547048362153975355 17286545320572543230963033)
      ·
        refine ⟨12964908990429407423222275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17286545320572543230963033 12964908990429407423222275)
        ·
          refine ⟨19447363485644111134833413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12964908990429407423222275 19447363485644111134833413)
          ·
            refine ⟨3646380653558270837781265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19447363485644111134833413 3646380653558270837781265)
            ·
              refine ⟨2734785490168703128335949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3646380653558270837781265 2734785490168703128335949)
              ·
                refine ⟨1025544558813263673125981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2734785490168703128335949 1025544558813263673125981)
                ·
                  refine ⟨384579209554973877422243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025544558813263673125981 384579209554973877422243)
                  ·
                    rfl

theorem cell20_842586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_842586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842586 prefixEnd_842586 := by exact prefixLift 842586
  have htrace : WordTrace (prefixWord ++ tailWord_842586) baseStart_842586 baseEnd_842586 := by
    simpa [prefixWord, tailWord_842586, baseEnd_842586] using wordTrace_append hprefix tailTrace_842586
  have hstable : (prefixWord ++ tailWord_842586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842586).length < 2 ^ (prefixWord ++ tailWord_842586).sum := by decide
  have hdescent : baseEnd_842586 < baseStart_842586 := by decide
  rcases family_descends (prefixWord ++ tailWord_842586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842606 : List Nat := [4, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_842606 : Nat := 118140960795 + 842606 * 2 ^ 59
def prefixEnd_842606 : Nat := 4983230072969 + 3 ^ 40 * 842606 * 2
def baseEnd_842606 : Nat := 384588338099942696755495

theorem tailTrace_842606 : CollatzResearch.WordTrace tailWord_842606 prefixEnd_842606 384588338099942696755495 := by
  unfold tailWord_842606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3841545698173730311624459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20488243723593228328663781 3841545698173730311624459)
  ·
    refine ⟨5762318547260595467436689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3841545698173730311624459 5762318547260595467436689)
    ·
      refine ⟨4321738910445446600577517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5762318547260595467436689 4321738910445446600577517)
      ·
        refine ⟨1620652091417042475216569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4321738910445446600577517 1620652091417042475216569)
        ·
          refine ⟨1215489068562781856412427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1620652091417042475216569 1215489068562781856412427)
          ·
            refine ⟨1823233602844172784618641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215489068562781856412427 1823233602844172784618641)
            ·
              refine ⟨1367425202133129588463981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823233602844172784618641 1367425202133129588463981)
              ·
                refine ⟨512784450799923595673993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1367425202133129588463981 512784450799923595673993)
                ·
                  refine ⟨384588338099942696755495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512784450799923595673993 384588338099942696755495)
                  ·
                    rfl

theorem cell20_842606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_842606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842606 prefixEnd_842606 := by exact prefixLift 842606
  have htrace : WordTrace (prefixWord ++ tailWord_842606) baseStart_842606 baseEnd_842606 := by
    simpa [prefixWord, tailWord_842606, baseEnd_842606] using wordTrace_append hprefix tailTrace_842606
  have hstable : (prefixWord ++ tailWord_842606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842606).length < 2 ^ (prefixWord ++ tailWord_842606).sum := by decide
  have hdescent : baseEnd_842606 < baseStart_842606 := by decide
  rcases family_descends (prefixWord ++ tailWord_842606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842610 : List Nat := [3, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_842610 : Nat := 118140960795 + 842610 * 2 ^ 59
def prefixEnd_842610 : Nat := 4983230072969 + 3 ^ 40 * 842610 * 2
def baseEnd_842610 : Nat := 384590163808936460622145

theorem tailTrace_842610 : CollatzResearch.WordTrace tailWord_842610 prefixEnd_842610 384590163808936460622145 := by
  unfold tailWord_842610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7683127869343837794035321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20488340984916900784094189 7683127869343837794035321)
  ·
    refine ⟨5762345902007878345526491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7683127869343837794035321 5762345902007878345526491)
    ·
      refine ⟨8643518853011817518289737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5762345902007878345526491 8643518853011817518289737)
      ·
        refine ⟨6482639139758863138717303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8643518853011817518289737 6482639139758863138717303)
        ·
          refine ⟨9723958709638294708075955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6482639139758863138717303 9723958709638294708075955)
          ·
            refine ⟨14585938064457442062113933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9723958709638294708075955 14585938064457442062113933)
            ·
              refine ⟨5469726774171540773292725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14585938064457442062113933 5469726774171540773292725)
              ·
                refine ⟨512786885078581947496193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5469726774171540773292725 512786885078581947496193)
                ·
                  refine ⟨384590163808936460622145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512786885078581947496193 384590163808936460622145)
                  ·
                    rfl

theorem cell20_842610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_842610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842610 prefixEnd_842610 := by exact prefixLift 842610
  have htrace : WordTrace (prefixWord ++ tailWord_842610) baseStart_842610 baseEnd_842610 := by
    simpa [prefixWord, tailWord_842610, baseEnd_842610] using wordTrace_append hprefix tailTrace_842610
  have hstable : (prefixWord ++ tailWord_842610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842610).length < 2 ^ (prefixWord ++ tailWord_842610).sum := by decide
  have hdescent : baseEnd_842610 < baseStart_842610 := by decide
  rcases family_descends (prefixWord ++ tailWord_842610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842631 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_842631 : Nat := 118140960795 + 842631 * 2 ^ 59
def prefixEnd_842631 : Nat := 4983230072969 + 3 ^ 40 * 842631 * 2
def baseEnd_842631 : Nat := 384599748781153720922059

theorem tailTrace_842631 : CollatzResearch.WordTrace tailWord_842631 prefixEnd_842631 384599748781153720922059 := by
  unfold tailWord_842631
  simp only [CollatzResearch.WordTrace]
  refine ⟨30733277410299271762655747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20488851606866181175103831 30733277410299271762655747)
  ·
    refine ⟨46099916115448907643983621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30733277410299271762655747 46099916115448907643983621)
    ·
      refine ⟨8643734271646670183246929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46099916115448907643983621 8643734271646670183246929)
      ·
        refine ⟨6482800703735002637435197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8643734271646670183246929 6482800703735002637435197)
        ·
          refine ⟨2431050263900625989038199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6482800703735002637435197 2431050263900625989038199)
          ·
            refine ⟨3646575395850938983557299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431050263900625989038199 3646575395850938983557299)
            ·
              refine ⟨5469863093776408475335949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646575395850938983557299 5469863093776408475335949)
              ·
                refine ⟨2051198660166153178250981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5469863093776408475335949 2051198660166153178250981)
                ·
                  refine ⟨384599748781153720922059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2051198660166153178250981 384599748781153720922059)
                  ·
                    rfl

theorem cell20_842631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_842631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842631 prefixEnd_842631 := by exact prefixLift 842631
  have htrace : WordTrace (prefixWord ++ tailWord_842631) baseStart_842631 baseEnd_842631 := by
    simpa [prefixWord, tailWord_842631, baseEnd_842631] using wordTrace_append hprefix tailTrace_842631
  have hstable : (prefixWord ++ tailWord_842631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842631).length < 2 ^ (prefixWord ++ tailWord_842631).sum := by decide
  have hdescent : baseEnd_842631 < baseStart_842631 := by decide
  rcases family_descends (prefixWord ++ tailWord_842631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842655 : List Nat := [1, 1, 2, 5, 2, 1, 4, 4]
def baseStart_842655 : Nat := 118140960795 + 842655 * 2 ^ 59
def prefixEnd_842655 : Nat := 4983230072969 + 3 ^ 40 * 842655 * 2
def baseEnd_842655 : Nat := 128203567678372101373987

theorem tailTrace_842655 : CollatzResearch.WordTrace tailWord_842655 prefixEnd_842655 128203567678372101373987 := by
  unfold tailWord_842655
  simp only [CollatzResearch.WordTrace]
  refine ⟨30734152762212323861529419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20489435174808215907686279 30734152762212323861529419)
  ·
    refine ⟨46101229143318485792294129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30734152762212323861529419 46101229143318485792294129)
    ·
      refine ⟨34575921857488864344220597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46101229143318485792294129 34575921857488864344220597)
      ·
        refine ⟨3241492674139581032270681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34575921857488864344220597 3241492674139581032270681)
        ·
          refine ⟨2431119505604685774203011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3241492674139581032270681 2431119505604685774203011)
          ·
            refine ⟨3646679258407028661304517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431119505604685774203011 3646679258407028661304517)
            ·
              refine ⟨683752360951317873994597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3646679258407028661304517 683752360951317873994597)
              ·
                refine ⟨128203567678372101373987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 683752360951317873994597 128203567678372101373987)
                ·
                  rfl

theorem cell20_842655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 4].length) (baseStart_842655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842655 prefixEnd_842655 := by exact prefixLift 842655
  have htrace : WordTrace (prefixWord ++ tailWord_842655) baseStart_842655 baseEnd_842655 := by
    simpa [prefixWord, tailWord_842655, baseEnd_842655] using wordTrace_append hprefix tailTrace_842655
  have hstable : (prefixWord ++ tailWord_842655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842655).length < 2 ^ (prefixWord ++ tailWord_842655).sum := by decide
  have hdescent : baseEnd_842655 < baseStart_842655 := by decide
  rcases family_descends (prefixWord ++ tailWord_842655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842678 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_842678 : Nat := 118140960795 + 842678 * 2 ^ 59
def prefixEnd_842678 : Nat := 4983230072969 + 3 ^ 40 * 842678 * 2
def baseEnd_842678 : Nat := 384621200861830446355201

theorem tailTrace_842678 : CollatzResearch.WordTrace tailWord_842678 prefixEnd_842678 384621200861830446355201 := by
  unfold tailWord_842678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1920936977570562424351043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20489994427419332526411125 1920936977570562424351043)
  ·
    refine ⟨2881405466355843636526565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1920936977570562424351043 2881405466355843636526565)
    ·
      refine ⟨540263524941720681848731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2881405466355843636526565 540263524941720681848731)
      ·
        refine ⟨810395287412581022773097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540263524941720681848731 810395287412581022773097)
        ·
          refine ⟨607796465559435767079823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810395287412581022773097 607796465559435767079823)
          ·
            refine ⟨911694698339153650619735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607796465559435767079823 911694698339153650619735)
            ·
              refine ⟨1367542047508730475929603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911694698339153650619735 1367542047508730475929603)
              ·
                refine ⟨2051313071263095713894405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367542047508730475929603 2051313071263095713894405)
                ·
                  refine ⟨384621200861830446355201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2051313071263095713894405 384621200861830446355201)
                  ·
                    rfl

theorem cell20_842678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_842678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842678 prefixEnd_842678 := by exact prefixLift 842678
  have htrace : WordTrace (prefixWord ++ tailWord_842678) baseStart_842678 baseEnd_842678 := by
    simpa [prefixWord, tailWord_842678, baseEnd_842678] using wordTrace_append hprefix tailTrace_842678
  have hstable : (prefixWord ++ tailWord_842678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842678).length < 2 ^ (prefixWord ++ tailWord_842678).sum := by decide
  have hdescent : baseEnd_842678 < baseStart_842678 := by decide
  rcases family_descends (prefixWord ++ tailWord_842678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842692 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 3]
def baseStart_842692 : Nat := 118140960795 + 842692 * 2 ^ 59
def prefixEnd_842692 : Nat := 4983230072969 + 3 ^ 40 * 842692 * 2
def baseEnd_842692 : Nat := 384627590843308619888477

theorem tailTrace_842692 : CollatzResearch.WordTrace tailWord_842692 prefixEnd_842692 384627590843308619888477 := by
  unfold tailWord_842692
  simp only [CollatzResearch.WordTrace]
  refine ⟨15367751131539139590313165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20490334842052186120417553 15367751131539139590313165)
  ·
    refine ⟨5762906674327177346367437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15367751131539139590313165 5762906674327177346367437)
    ·
      refine ⟨2161090002872691504887789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5762906674327177346367437 2161090002872691504887789)
      ·
        refine ⟨810408751077259314332921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2161090002872691504887789 810408751077259314332921)
        ·
          refine ⟨607806563307944485749691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 810408751077259314332921 607806563307944485749691)
          ·
            refine ⟨911709844961916728624537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607806563307944485749691 911709844961916728624537)
            ·
              refine ⟨683782383721437546468403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911709844961916728624537 683782383721437546468403)
              ·
                refine ⟨1025673575582156319702605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683782383721437546468403 1025673575582156319702605)
                ·
                  refine ⟨384627590843308619888477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025673575582156319702605 384627590843308619888477)
                  ·
                    rfl

theorem cell20_842692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_842692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842692 prefixEnd_842692 := by exact prefixLift 842692
  have htrace : WordTrace (prefixWord ++ tailWord_842692) baseStart_842692 baseEnd_842692 := by
    simpa [prefixWord, tailWord_842692, baseEnd_842692] using wordTrace_append hprefix tailTrace_842692
  have hstable : (prefixWord ++ tailWord_842692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842692).length < 2 ^ (prefixWord ++ tailWord_842692).sum := by decide
  have hdescent : baseEnd_842692 < baseStart_842692 := by decide
  rcases family_descends (prefixWord ++ tailWord_842692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842696 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 3]
def baseStart_842696 : Nat := 118140960795 + 842696 * 2 ^ 59
def prefixEnd_842696 : Nat := 4983230072969 + 3 ^ 40 * 842696 * 2
def baseEnd_842696 : Nat := 384629416552302383755127

theorem tailTrace_842696 : CollatzResearch.WordTrace tailWord_842696 prefixEnd_842696 384629416552302383755127 := by
  unfold tailWord_842696
  simp only [CollatzResearch.WordTrace]
  refine ⟨15367824077531893931885971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20490432103375858575847961 15367824077531893931885971)
  ·
    refine ⟨23051736116297840897828957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15367824077531893931885971 23051736116297840897828957)
    ·
      refine ⟨8644401043611690336685859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23051736116297840897828957 8644401043611690336685859)
      ·
        refine ⟨12966601565417535505028789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8644401043611690336685859 12966601565417535505028789)
        ·
          refine ⟨1215618896757893953596449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12966601565417535505028789 1215618896757893953596449)
          ·
            refine ⟨911714172568420465197337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215618896757893953596449 911714172568420465197337)
            ·
              refine ⟨683785629426315348898003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911714172568420465197337 683785629426315348898003)
              ·
                refine ⟨1025678444139473023347005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683785629426315348898003 1025678444139473023347005)
                ·
                  refine ⟨384629416552302383755127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025678444139473023347005 384629416552302383755127)
                  ·
                    rfl

theorem cell20_842696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_842696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842696 prefixEnd_842696 := by exact prefixLift 842696
  have htrace : WordTrace (prefixWord ++ tailWord_842696) baseStart_842696 baseEnd_842696 := by
    simpa [prefixWord, tailWord_842696, baseEnd_842696] using wordTrace_append hprefix tailTrace_842696
  have hstable : (prefixWord ++ tailWord_842696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842696).length < 2 ^ (prefixWord ++ tailWord_842696).sum := by decide
  have hdescent : baseEnd_842696 < baseStart_842696 := by decide
  rcases family_descends (prefixWord ++ tailWord_842696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842700 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_842700 : Nat := 118140960795 + 842700 * 2 ^ 59
def prefixEnd_842700 : Nat := 4983230072969 + 3 ^ 40 * 842700 * 2
def baseEnd_842700 : Nat := 384631242261296147621777

theorem tailTrace_842700 : CollatzResearch.WordTrace tailWord_842700 prefixEnd_842700 384631242261296147621777 := by
  unfold tailWord_842700
  simp only [CollatzResearch.WordTrace]
  refine ⟨15367897023524648273458777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20490529364699531031278369 15367897023524648273458777)
  ·
    refine ⟨11525922767643486205094083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15367897023524648273458777 11525922767643486205094083)
    ·
      refine ⟨17288884151465229307641125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11525922767643486205094083 17288884151465229307641125)
      ·
        refine ⟨3241665778399730495182711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17288884151465229307641125 3241665778399730495182711)
        ·
          refine ⟨4862498667599595742774067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3241665778399730495182711 4862498667599595742774067)
          ·
            refine ⟨7293748001399393614161101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4862498667599595742774067 7293748001399393614161101)
            ·
              refine ⟨2735155500524772605310413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7293748001399393614161101 2735155500524772605310413)
              ·
                refine ⟨1025683312696789726991405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2735155500524772605310413 1025683312696789726991405)
                ·
                  refine ⟨384631242261296147621777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025683312696789726991405 384631242261296147621777)
                  ·
                    rfl

theorem cell20_842700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_842700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842700 prefixEnd_842700 := by exact prefixLift 842700
  have htrace : WordTrace (prefixWord ++ tailWord_842700) baseStart_842700 baseEnd_842700 := by
    simpa [prefixWord, tailWord_842700, baseEnd_842700] using wordTrace_append hprefix tailTrace_842700
  have hstable : (prefixWord ++ tailWord_842700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842700).length < 2 ^ (prefixWord ++ tailWord_842700).sum := by decide
  have hdescent : baseEnd_842700 < baseStart_842700 := by decide
  rcases family_descends (prefixWord ++ tailWord_842700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842714 : List Nat := [3, 1, 1, 2, 4, 1, 2, 6]
def baseStart_842714 : Nat := 118140960795 + 842714 * 2 ^ 59
def prefixEnd_842714 : Nat := 4983230072969 + 3 ^ 40 * 842714 * 2
def baseEnd_842714 : Nat := 128212544080924773718351

theorem tailTrace_842714 : CollatzResearch.WordTrace tailWord_842714 prefixEnd_842714 128212544080924773718351 := by
  unfold tailWord_842714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7684076167249644234481799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20490869779332384625284797 7684076167249644234481799)
  ·
    refine ⟨11526114250874466351722699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7684076167249644234481799 11526114250874466351722699)
    ·
      refine ⟨17289171376311699527584049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11526114250874466351722699 17289171376311699527584049)
      ·
        refine ⟨12966878532233774645688037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17289171376311699527584049 12966878532233774645688037)
        ·
          refine ⟨2431289724793832746066507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12966878532233774645688037 2431289724793832746066507)
          ·
            refine ⟨3646934587190749119099761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431289724793832746066507 3646934587190749119099761)
            ·
              refine ⟨2735200940393061839324821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3646934587190749119099761 2735200940393061839324821)
              ·
                refine ⟨128212544080924773718351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2735200940393061839324821 128212544080924773718351)
                ·
                  rfl

theorem cell20_842714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_842714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842714 prefixEnd_842714 := by exact prefixLift 842714
  have htrace : WordTrace (prefixWord ++ tailWord_842714) baseStart_842714 baseEnd_842714 := by
    simpa [prefixWord, tailWord_842714, baseEnd_842714] using wordTrace_append hprefix tailTrace_842714
  have hstable : (prefixWord ++ tailWord_842714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842714).length < 2 ^ (prefixWord ++ tailWord_842714).sum := by decide
  have hdescent : baseEnd_842714 < baseStart_842714 := by decide
  rcases family_descends (prefixWord ++ tailWord_842714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842735 : List Nat := [1, 1, 2, 1, 4, 11]
def baseStart_842735 : Nat := 118140960795 + 842735 * 2 ^ 59
def prefixEnd_842735 : Nat := 4983230072969 + 3 ^ 40 * 842735 * 2
def baseEnd_842735 : Nat := 14246193230184873387221

theorem tailTrace_842735 : CollatzResearch.WordTrace tailWord_842735 prefixEnd_842735 14246193230184873387221 := by
  unfold tailWord_842735
  simp only [CollatzResearch.WordTrace]
  refine ⟨30737070601922497524441659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20491380401281665016294439 30737070601922497524441659)
  ·
    refine ⟨46105605902883746286662489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30737070601922497524441659 46105605902883746286662489)
    ·
      refine ⟨34579204427162809714996867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46105605902883746286662489 34579204427162809714996867)
      ·
        refine ⟨51868806640744214572495301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34579204427162809714996867 51868806640744214572495301)
        ·
          refine ⟨9725401245139540232342869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51868806640744214572495301 9725401245139540232342869)
          ·
            refine ⟨14246193230184873387221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9725401245139540232342869 14246193230184873387221)
            ·
              rfl

theorem cell20_842735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 11].length) (baseStart_842735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842735 prefixEnd_842735 := by exact prefixLift 842735
  have htrace : WordTrace (prefixWord ++ tailWord_842735) baseStart_842735 baseEnd_842735 := by
    simpa [prefixWord, tailWord_842735, baseEnd_842735] using wordTrace_append hprefix tailTrace_842735
  have hstable : (prefixWord ++ tailWord_842735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842735).length < 2 ^ (prefixWord ++ tailWord_842735).sum := by decide
  have hdescent : baseEnd_842735 < baseStart_842735 := by decide
  rcases family_descends (prefixWord ++ tailWord_842735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842849 : List Nat := [1, 2, 3, 1, 1, 2, 10]
def baseStart_842849 : Nat := 118140960795 + 842849 * 2 ^ 59
def prefixEnd_842849 : Nat := 4983230072969 + 3 ^ 40 * 842849 * 2
def baseEnd_842849 : Nat := 42744361102368205739389

theorem tailTrace_842849 : CollatzResearch.WordTrace tailWord_842849 prefixEnd_842849 42744361102368205739389 := by
  unfold tailWord_842849
  simp only [CollatzResearch.WordTrace]
  refine ⟨30741228523509494994091601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20494152349006329996061067 30741228523509494994091601)
  ·
    refine ⟨23055921392632121245568701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30741228523509494994091601 23055921392632121245568701)
    ·
      refine ⟨8645970522237045467088263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23055921392632121245568701 8645970522237045467088263)
      ·
        refine ⟨12968955783355568200632395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645970522237045467088263 12968955783355568200632395)
        ·
          refine ⟨19453433675033352300948593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12968955783355568200632395 19453433675033352300948593)
          ·
            refine ⟨14590075256275014225711445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19453433675033352300948593 14590075256275014225711445)
            ·
              refine ⟨42744361102368205739389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14590075256275014225711445 42744361102368205739389)
              ·
                rfl

theorem cell20_842849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 10].length) (baseStart_842849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842849 prefixEnd_842849 := by exact prefixLift 842849
  have htrace : WordTrace (prefixWord ++ tailWord_842849) baseStart_842849 baseEnd_842849 := by
    simpa [prefixWord, tailWord_842849, baseEnd_842849] using wordTrace_append hprefix tailTrace_842849
  have hstable : (prefixWord ++ tailWord_842849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842849).length < 2 ^ (prefixWord ++ tailWord_842849).sum := by decide
  have hdescent : baseEnd_842849 < baseStart_842849 := by decide
  rcases family_descends (prefixWord ++ tailWord_842849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842855 : List Nat := [1, 1, 5, 1, 1, 4, 3, 2, 2]
def baseStart_842855 : Nat := 118140960795 + 842855 * 2 ^ 59
def prefixEnd_842855 : Nat := 4983230072969 + 3 ^ 40 * 842855 * 2
def baseEnd_842855 : Nat := 384701988484804497454477

theorem tailTrace_842855 : CollatzResearch.WordTrace tailWord_842855 prefixEnd_842855 384701988484804497454477 := by
  unfold tailWord_842855
  simp only [CollatzResearch.WordTrace]
  refine ⟨30741447361487758018810019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20494298240991838679206679 30741447361487758018810019)
  ·
    refine ⟨46112171042231637028215029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30741447361487758018810019 46112171042231637028215029)
    ·
      refine ⟨4323016035209215971395159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46112171042231637028215029 4323016035209215971395159)
      ·
        refine ⟨6484524052813823957092739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323016035209215971395159 6484524052813823957092739)
        ·
          refine ⟨9726786079220735935639109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6484524052813823957092739 9726786079220735935639109)
          ·
            refine ⟨1823772389853887987932333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9726786079220735935639109 1823772389853887987932333)
            ·
              refine ⟨683914646195207995474625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1823772389853887987932333 683914646195207995474625)
              ·
                refine ⟨512935984646405996605969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683914646195207995474625 512935984646405996605969)
                ·
                  refine ⟨384701988484804497454477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512935984646405996605969 384701988484804497454477)
                  ·
                    rfl

theorem cell20_842855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 2, 2].length) (baseStart_842855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842855 prefixEnd_842855 := by exact prefixLift 842855
  have htrace : WordTrace (prefixWord ++ tailWord_842855) baseStart_842855 baseEnd_842855 := by
    simpa [prefixWord, tailWord_842855, baseEnd_842855] using wordTrace_append hprefix tailTrace_842855
  have hstable : (prefixWord ++ tailWord_842855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842855).length < 2 ^ (prefixWord ++ tailWord_842855).sum := by decide
  have hdescent : baseEnd_842855 < baseStart_842855 := by decide
  rcases family_descends (prefixWord ++ tailWord_842855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842866 : List Nat := [3, 2, 1, 2, 2, 1, 4, 5]
def baseStart_842866 : Nat := 118140960795 + 842866 * 2 ^ 59
def prefixEnd_842866 : Nat := 4983230072969 + 3 ^ 40 * 842866 * 2
def baseEnd_842866 : Nat := 128235669728179116029255

theorem tailTrace_842866 : CollatzResearch.WordTrace tailWord_842866 prefixEnd_842866 128235669728179116029255 := by
  unfold tailWord_842866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685462141111976724365113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20494565709631937931640301 7685462141111976724365113)
  ·
    refine ⟨5764096605833982543273835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7685462141111976724365113 5764096605833982543273835)
    ·
      refine ⟨8646144908750973814910753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5764096605833982543273835 8646144908750973814910753)
      ·
        refine ⟨6484608681563230361183065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8646144908750973814910753 6484608681563230361183065)
        ·
          refine ⟨4863456511172422770887299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6484608681563230361183065 4863456511172422770887299)
          ·
            refine ⟨7295184766758634156330949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863456511172422770887299 7295184766758634156330949)
            ·
              refine ⟨1367847143767243904312053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7295184766758634156330949 1367847143767243904312053)
              ·
                refine ⟨128235669728179116029255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1367847143767243904312053 128235669728179116029255)
                ·
                  rfl

theorem cell20_842866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_842866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842866 prefixEnd_842866 := by exact prefixLift 842866
  have htrace : WordTrace (prefixWord ++ tailWord_842866) baseStart_842866 baseEnd_842866 := by
    simpa [prefixWord, tailWord_842866, baseEnd_842866] using wordTrace_append hprefix tailTrace_842866
  have hstable : (prefixWord ++ tailWord_842866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842866).length < 2 ^ (prefixWord ++ tailWord_842866).sum := by decide
  have hdescent : baseEnd_842866 < baseStart_842866 := by decide
  rcases family_descends (prefixWord ++ tailWord_842866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842880 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_842880 : Nat := 118140960795 + 842880 * 2 ^ 59
def prefixEnd_842880 : Nat := 4983230072969 + 3 ^ 40 * 842880 * 2
def baseEnd_842880 : Nat := 384713399166015521621041

theorem tailTrace_842880 : CollatzResearch.WordTrace tailWord_842880 prefixEnd_842880 384713399166015521621041 := by
  unfold tailWord_842880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15371179593198593644235047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20494906124264791525646729 15371179593198593644235047)
  ·
    refine ⟨23056769389797890466352571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15371179593198593644235047 23056769389797890466352571)
    ·
      refine ⟨34585154084696835699528857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23056769389797890466352571 34585154084696835699528857)
      ·
        refine ⟨25938865563522626774646643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34585154084696835699528857 25938865563522626774646643)
        ·
          refine ⟨38908298345283940161969965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25938865563522626774646643 38908298345283940161969965)
          ·
            refine ⟨14590611879481477560738737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38908298345283940161969965 14590611879481477560738737)
            ·
              refine ⟨10942958909611108170554053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14590611879481477560738737 10942958909611108170554053)
              ·
                refine ⟨2051804795552082781978885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10942958909611108170554053 2051804795552082781978885)
                ·
                  refine ⟨384713399166015521621041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2051804795552082781978885 384713399166015521621041)
                  ·
                    rfl

theorem cell20_842880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_842880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842880 prefixEnd_842880 := by exact prefixLift 842880
  have htrace : WordTrace (prefixWord ++ tailWord_842880) baseStart_842880 baseEnd_842880 := by
    simpa [prefixWord, tailWord_842880, baseEnd_842880] using wordTrace_append hprefix tailTrace_842880
  have hstable : (prefixWord ++ tailWord_842880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842880).length < 2 ^ (prefixWord ++ tailWord_842880).sum := by decide
  have hdescent : baseEnd_842880 < baseStart_842880 := by decide
  rcases family_descends (prefixWord ++ tailWord_842880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_842910 : List Nat := [4, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_842910 : Nat := 118140960795 + 842910 * 2 ^ 59
def prefixEnd_842910 : Nat := 4983230072969 + 3 ^ 40 * 842910 * 2
def baseEnd_842910 : Nat := 384727091983468750620919

theorem tailTrace_842910 : CollatzResearch.WordTrace tailWord_842910 prefixEnd_842910 384727091983468750620919 := by
  unfold tailWord_842910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842931672036062801507773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20495635584192334941374789 3842931672036062801507773)
  ·
    refine ⟨1441099377013523550565415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3842931672036062801507773 1441099377013523550565415)
    ·
      refine ⟨2161649065520285325848123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441099377013523550565415 2161649065520285325848123)
      ·
        refine ⟨3242473598280427988772185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161649065520285325848123 3242473598280427988772185)
        ·
          refine ⟨2431855198710320991579139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3242473598280427988772185 2431855198710320991579139)
          ·
            refine ⟨3647782798065481487368709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431855198710320991579139 3647782798065481487368709)
            ·
              refine ⟨683959274637277778881633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3647782798065481487368709 683959274637277778881633)
              ·
                refine ⟨512969455977958334161225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683959274637277778881633 512969455977958334161225)
                ·
                  refine ⟨384727091983468750620919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512969455977958334161225 384727091983468750620919)
                  ·
                    rfl

theorem cell20_842910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_842910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_842910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_842910 prefixEnd_842910 := by exact prefixLift 842910
  have htrace : WordTrace (prefixWord ++ tailWord_842910) baseStart_842910 baseEnd_842910 := by
    simpa [prefixWord, tailWord_842910, baseEnd_842910] using wordTrace_append hprefix tailTrace_842910
  have hstable : (prefixWord ++ tailWord_842910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_842910).length < 2 ^ (prefixWord ++ tailWord_842910).sum := by decide
  have hdescent : baseEnd_842910 < baseStart_842910 := by decide
  rcases family_descends (prefixWord ++ tailWord_842910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843001 : List Nat := [1, 2, 1, 3, 1, 1, 5, 6]
def baseStart_843001 : Nat := 118140960795 + 843001 * 2 ^ 59
def prefixEnd_843001 : Nat := 4983230072969 + 3 ^ 40 * 843001 * 2
def baseEnd_843001 : Nat := 128256208954358959529071

theorem tailTrace_843001 : CollatzResearch.WordTrace tailWord_843001 prefixEnd_843001 128256208954358959529071 := by
  unfold tailWord_843001
  simp only [CollatzResearch.WordTrace]
  refine ⟨30746772418958824953624857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20497848279305883302416571 30746772418958824953624857)
  ·
    refine ⟨23060079314219118715218643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30746772418958824953624857 23060079314219118715218643)
    ·
      refine ⟨34590118971328678072827965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23060079314219118715218643 34590118971328678072827965)
      ·
        refine ⟨12971294614248254277310487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34590118971328678072827965 12971294614248254277310487)
        ·
          refine ⟨19456941921372381415965731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12971294614248254277310487 19456941921372381415965731)
          ·
            refine ⟨29185412882058572123948597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19456941921372381415965731 29185412882058572123948597)
            ·
              refine ⟨2736132457692991136620181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29185412882058572123948597 2736132457692991136620181)
              ·
                refine ⟨128256208954358959529071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2736132457692991136620181 128256208954358959529071)
                ·
                  rfl

theorem cell20_843001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_843001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843001 prefixEnd_843001 := by exact prefixLift 843001
  have htrace : WordTrace (prefixWord ++ tailWord_843001) baseStart_843001 baseEnd_843001 := by
    simpa [prefixWord, tailWord_843001, baseEnd_843001] using wordTrace_append hprefix tailTrace_843001
  have hstable : (prefixWord ++ tailWord_843001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843001).length < 2 ^ (prefixWord ++ tailWord_843001).sum := by decide
  have hdescent : baseEnd_843001 < baseStart_843001 := by decide
  rcases family_descends (prefixWord ++ tailWord_843001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843025 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 3]
def baseStart_843025 : Nat := 118140960795 + 843025 * 2 ^ 59
def prefixEnd_843025 : Nat := 4983230072969 + 3 ^ 40 * 843025 * 2
def baseEnd_843025 : Nat := 384779581117039461787115

theorem tailTrace_843025 : CollatzResearch.WordTrace tailWord_843025 prefixEnd_843025 384779581117039461787115 := by
  unfold tailWord_843025
  simp only [CollatzResearch.WordTrace]
  refine ⟨30747647770871877052498529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20498431847247918034999019 30747647770871877052498529)
  ·
    refine ⟨23060735828153907789373897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30747647770871877052498529 23060735828153907789373897)
    ·
      refine ⟨17295551871115430842030423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23060735828153907789373897 17295551871115430842030423)
      ·
        refine ⟨25943327806673146263045635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17295551871115430842030423 25943327806673146263045635)
        ·
          refine ⟨38914991710009719394568453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25943327806673146263045635 38914991710009719394568453)
          ·
            refine ⟨7296560945626822386481585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38914991710009719394568453 7296560945626822386481585)
            ·
              refine ⟨5472420709220116789861189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7296560945626822386481585 5472420709220116789861189)
              ·
                refine ⟨1026078882978771898098973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5472420709220116789861189 1026078882978771898098973)
                ·
                  refine ⟨384779581117039461787115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026078882978771898098973 384779581117039461787115)
                  ·
                    rfl

theorem cell20_843025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_843025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843025 prefixEnd_843025 := by exact prefixLift 843025
  have htrace : WordTrace (prefixWord ++ tailWord_843025) baseStart_843025 baseEnd_843025 := by
    simpa [prefixWord, tailWord_843025, baseEnd_843025] using wordTrace_append hprefix tailTrace_843025
  have hstable : (prefixWord ++ tailWord_843025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843025).length < 2 ^ (prefixWord ++ tailWord_843025).sum := by decide
  have hdescent : baseEnd_843025 < baseStart_843025 := by decide
  rcases family_descends (prefixWord ++ tailWord_843025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843038 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_843038 : Nat := 118140960795 + 843038 * 2 ^ 59
def prefixEnd_843038 : Nat := 4983230072969 + 3 ^ 40 * 843038 * 2
def baseEnd_843038 : Nat := 384785514671269194353729

theorem tailTrace_843038 : CollatzResearch.WordTrace tailWord_843038 prefixEnd_843038 384785514671269194353729 := by
  unfold tailWord_843038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843515239978097534090221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20498747946549853515147845 3843515239978097534090221)
  ·
    refine ⟨1441318214991786575283833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3843515239978097534090221 1441318214991786575283833)
    ·
      refine ⟨1080988661243839931462875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1441318214991786575283833 1080988661243839931462875)
      ·
        refine ⟨1621482991865759897194313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080988661243839931462875 1621482991865759897194313)
        ·
          refine ⟨1216112243899319922895735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1621482991865759897194313 1216112243899319922895735)
          ·
            refine ⟨1824168365848979884343603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216112243899319922895735 1824168365848979884343603)
            ·
              refine ⟨2736252548773469826515405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824168365848979884343603 2736252548773469826515405)
              ·
                refine ⟨1026094705790051184943277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2736252548773469826515405 1026094705790051184943277)
                ·
                  refine ⟨384785514671269194353729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026094705790051184943277 384785514671269194353729)
                  ·
                    rfl

theorem cell20_843038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_843038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843038 prefixEnd_843038 := by exact prefixLift 843038
  have htrace : WordTrace (prefixWord ++ tailWord_843038) baseStart_843038 baseEnd_843038 := by
    simpa [prefixWord, tailWord_843038, baseEnd_843038] using wordTrace_append hprefix tailTrace_843038
  have hstable : (prefixWord ++ tailWord_843038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843038).length < 2 ^ (prefixWord ++ tailWord_843038).sum := by decide
  have hdescent : baseEnd_843038 < baseStart_843038 := by decide
  rcases family_descends (prefixWord ++ tailWord_843038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843108 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_843108 : Nat := 118140960795 + 843108 * 2 ^ 59
def prefixEnd_843108 : Nat := 4983230072969 + 3 ^ 40 * 843108 * 2
def baseEnd_843108 : Nat := 384817464578660062020109

theorem tailTrace_843108 : CollatzResearch.WordTrace tailWord_843108 prefixEnd_843108 384817464578660062020109 := by
  unfold tailWord_843108
  simp only [CollatzResearch.WordTrace]
  refine ⟨15375337514785591113884989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20500450019714121485179985 15375337514785591113884989)
  ·
    refine ⟨5765751568044596667706871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15375337514785591113884989 5765751568044596667706871)
    ·
      refine ⟨8648627352066895001560307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5765751568044596667706871 8648627352066895001560307)
      ·
        refine ⟨12972941028100342502340461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8648627352066895001560307 12972941028100342502340461)
        ·
          refine ⟨4864852885537628438377673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12972941028100342502340461 4864852885537628438377673)
          ·
            refine ⟨3648639664153221328783255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4864852885537628438377673 3648639664153221328783255)
            ·
              refine ⟨5472959496229831993174883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648639664153221328783255 5472959496229831993174883)
              ·
                refine ⟨8209439244344747989762325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5472959496229831993174883 8209439244344747989762325)
                ·
                  refine ⟨384817464578660062020109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8209439244344747989762325 384817464578660062020109)
                  ·
                    rfl

theorem cell20_843108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_843108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843108 prefixEnd_843108 := by exact prefixLift 843108
  have htrace : WordTrace (prefixWord ++ tailWord_843108) baseStart_843108 baseEnd_843108 := by
    simpa [prefixWord, tailWord_843108, baseEnd_843108] using wordTrace_append hprefix tailTrace_843108
  have hstable : (prefixWord ++ tailWord_843108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843108).length < 2 ^ (prefixWord ++ tailWord_843108).sum := by decide
  have hdescent : baseEnd_843108 < baseStart_843108 := by decide
  rcases family_descends (prefixWord ++ tailWord_843108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843111 : List Nat := [1, 1, 5, 1, 4, 1, 3, 4]
def baseStart_843111 : Nat := 118140960795 + 843111 * 2 ^ 59
def prefixEnd_843111 : Nat := 4983230072969 + 3 ^ 40 * 843111 * 2
def baseEnd_843111 : Nat := 128272944620135128306699

theorem tailTrace_843111 : CollatzResearch.WordTrace tailWord_843111 prefixEnd_843111 128272944620135128306699 := by
  unfold tailWord_843111
  simp only [CollatzResearch.WordTrace]
  refine ⟨30750784448560313740129187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20500522965706875826752791 30750784448560313740129187)
  ·
    refine ⟨46126176672840470610193781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30750784448560313740129187 46126176672840470610193781)
    ·
      refine ⟨4324329063078794119705667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46126176672840470610193781 4324329063078794119705667)
      ·
        refine ⟨6486493594618191179558501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4324329063078794119705667 6486493594618191179558501)
        ·
          refine ⟨1216217548990910846167219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6486493594618191179558501 1216217548990910846167219)
          ·
            refine ⟨1824326323486366269250829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216217548990910846167219 1824326323486366269250829)
            ·
              refine ⟨684122371307387350969061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1824326323486366269250829 684122371307387350969061)
              ·
                refine ⟨128272944620135128306699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684122371307387350969061 128272944620135128306699)
                ·
                  rfl

theorem cell20_843111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 4].length) (baseStart_843111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843111 prefixEnd_843111 := by exact prefixLift 843111
  have htrace : WordTrace (prefixWord ++ tailWord_843111) baseStart_843111 baseEnd_843111 := by
    simpa [prefixWord, tailWord_843111, baseEnd_843111] using wordTrace_append hprefix tailTrace_843111
  have hstable : (prefixWord ++ tailWord_843111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843111).length < 2 ^ (prefixWord ++ tailWord_843111).sum := by decide
  have hdescent : baseEnd_843111 < baseStart_843111 := by decide
  rcases family_descends (prefixWord ++ tailWord_843111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843139 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_843139 : Nat := 118140960795 + 843139 * 2 ^ 59
def prefixEnd_843139 : Nat := 4983230072969 + 3 ^ 40 * 843139 * 2
def baseEnd_843139 : Nat := 384831613823361731986649

theorem tailTrace_843139 : CollatzResearch.WordTrace tailWord_843139 prefixEnd_843139 384831613823361731986649 := by
  unfold tailWord_843139
  simp only [CollatzResearch.WordTrace]
  refine ⟨30751805692458874522148471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20501203794972583014765647 30751805692458874522148471)
  ·
    refine ⟨46127708538688311783222707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30751805692458874522148471 46127708538688311783222707)
    ·
      refine ⟨69191562808032467674834061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46127708538688311783222707 69191562808032467674834061)
      ·
        refine ⟨25946836053012175378062773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69191562808032467674834061 25946836053012175378062773)
        ·
          refine ⟨2432515879969891441693385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25946836053012175378062773 2432515879969891441693385)
          ·
            refine ⟨1824386909977418581270039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2432515879969891441693385 1824386909977418581270039)
            ·
              refine ⟨2736580364966127871905059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824386909977418581270039 2736580364966127871905059)
              ·
                refine ⟨4104870547449191807857589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2736580364966127871905059 4104870547449191807857589)
                ·
                  refine ⟨384831613823361731986649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4104870547449191807857589 384831613823361731986649)
                  ·
                    rfl

theorem cell20_843139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_843139 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843139 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843139 prefixEnd_843139 := by exact prefixLift 843139
  have htrace : WordTrace (prefixWord ++ tailWord_843139) baseStart_843139 baseEnd_843139 := by
    simpa [prefixWord, tailWord_843139, baseEnd_843139] using wordTrace_append hprefix tailTrace_843139
  have hstable : (prefixWord ++ tailWord_843139).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843139).length < 2 ^ (prefixWord ++ tailWord_843139).sum := by decide
  have hdescent : baseEnd_843139 < baseStart_843139 := by decide
  rcases family_descends (prefixWord ++ tailWord_843139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843170 : List Nat := [3, 3, 1, 2, 1, 3, 1, 6]
def baseStart_843170 : Nat := 118140960795 + 843170 * 2 ^ 59
def prefixEnd_843170 : Nat := 4983230072969 + 3 ^ 40 * 843170 * 2
def baseEnd_843170 : Nat := 128281921022687800651063

theorem tailTrace_843170 : CollatzResearch.WordTrace tailWord_843170 prefixEnd_843170 128281921022687800651063 := by
  unfold tailWord_843170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688234088836641704131741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20501957570231044544351309 7688234088836641704131741)
  ·
    refine ⟨2883087783313740639049403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7688234088836641704131741 2883087783313740639049403)
    ·
      refine ⟨4324631674970610958574105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883087783313740639049403 4324631674970610958574105)
      ·
        refine ⟨3243473756227958218930579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4324631674970610958574105 3243473756227958218930579)
        ·
          refine ⟨4865210634341937328395869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243473756227958218930579 4865210634341937328395869)
          ·
            refine ⟨1824453987878226498148451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4865210634341937328395869 1824453987878226498148451)
            ·
              refine ⟨2736680981817339747222677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824453987878226498148451 2736680981817339747222677)
              ·
                refine ⟨128281921022687800651063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2736680981817339747222677 128281921022687800651063)
                ·
                  rfl

theorem cell20_843170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_843170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843170 prefixEnd_843170 := by exact prefixLift 843170
  have htrace : WordTrace (prefixWord ++ tailWord_843170) baseStart_843170 baseEnd_843170 := by
    simpa [prefixWord, tailWord_843170, baseEnd_843170] using wordTrace_append hprefix tailTrace_843170
  have hstable : (prefixWord ++ tailWord_843170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843170).length < 2 ^ (prefixWord ++ tailWord_843170).sum := by decide
  have hdescent : baseEnd_843170 < baseStart_843170 := by decide
  rcases family_descends (prefixWord ++ tailWord_843170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843176 : List Nat := [2, 1, 6, 1, 2, 2, 1, 3, 2]
def baseStart_843176 : Nat := 118140960795 + 843176 * 2 ^ 59
def prefixEnd_843176 : Nat := 4983230072969 + 3 ^ 40 * 843176 * 2
def baseEnd_843176 : Nat := 384848501631554047753165

theorem tailTrace_843176 : CollatzResearch.WordTrace tailWord_843176 prefixEnd_843176 384848501631554047753165 := by
  unfold tailWord_843176
  simp only [CollatzResearch.WordTrace]
  refine ⟨15376577596662414920622691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20502103462216553227496921 15376577596662414920622691)
  ·
    refine ⟨23064866394993622380934037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15376577596662414920622691 23064866394993622380934037)
    ·
      refine ⟨1081165612265326049106283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23064866394993622380934037 1081165612265326049106283)
      ·
        refine ⟨1621748418397989073659425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081165612265326049106283 1621748418397989073659425)
        ·
          refine ⟨1216311313798491805244569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1621748418397989073659425 1216311313798491805244569)
          ·
            refine ⟨912233485348868853933427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1216311313798491805244569 912233485348868853933427)
            ·
              refine ⟨1368350228023303280900141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912233485348868853933427 1368350228023303280900141)
              ·
                refine ⟨513131335508738730337553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1368350228023303280900141 513131335508738730337553)
                ·
                  refine ⟨384848501631554047753165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513131335508738730337553 384848501631554047753165)
                  ·
                    rfl

theorem cell20_843176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_843176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843176 prefixEnd_843176 := by exact prefixLift 843176
  have htrace : WordTrace (prefixWord ++ tailWord_843176) baseStart_843176 baseEnd_843176 := by
    simpa [prefixWord, tailWord_843176, baseEnd_843176] using wordTrace_append hprefix tailTrace_843176
  have hstable : (prefixWord ++ tailWord_843176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843176).length < 2 ^ (prefixWord ++ tailWord_843176).sum := by decide
  have hdescent : baseEnd_843176 < baseStart_843176 := by decide
  rcases family_descends (prefixWord ++ tailWord_843176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843236 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_843236 : Nat := 118140960795 + 843236 * 2 ^ 59
def prefixEnd_843236 : Nat := 4983230072969 + 3 ^ 40 * 843236 * 2
def baseEnd_843236 : Nat := 384875887266460505752919

theorem tailTrace_843236 : CollatzResearch.WordTrace tailWord_843236 prefixEnd_843236 384875887266460505752919 := by
  unfold tailWord_843236
  simp only [CollatzResearch.WordTrace]
  refine ⟨15377671786553730044214781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20503562382071640058953041 15377671786553730044214781)
  ·
    refine ⟨5766626919957648766580543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15377671786553730044214781 5766626919957648766580543)
    ·
      refine ⟨8649940379936473149870815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5766626919957648766580543 8649940379936473149870815)
      ·
        refine ⟨12974910569904709724806223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8649940379936473149870815 12974910569904709724806223)
        ·
          refine ⟨19462365854857064587209335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12974910569904709724806223 19462365854857064587209335)
          ·
            refine ⟨29193548782285596880814003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19462365854857064587209335 29193548782285596880814003)
            ·
              refine ⟨43790323173428395321221005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29193548782285596880814003 43790323173428395321221005)
              ·
                refine ⟨16421371190035648245457877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43790323173428395321221005 16421371190035648245457877)
                ·
                  refine ⟨384875887266460505752919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16421371190035648245457877 384875887266460505752919)
                  ·
                    rfl

theorem cell20_843236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_843236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843236 prefixEnd_843236 := by exact prefixLift 843236
  have htrace : WordTrace (prefixWord ++ tailWord_843236) baseStart_843236 baseEnd_843236 := by
    simpa [prefixWord, tailWord_843236, baseEnd_843236] using wordTrace_append hprefix tailTrace_843236
  have hstable : (prefixWord ++ tailWord_843236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843236).length < 2 ^ (prefixWord ++ tailWord_843236).sum := by decide
  have hdescent : baseEnd_843236 < baseStart_843236 := by decide
  rcases family_descends (prefixWord ++ tailWord_843236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843243 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_843243 : Nat := 118140960795 + 843243 * 2 ^ 59
def prefixEnd_843243 : Nat := 4983230072969 + 3 ^ 40 * 843243 * 2
def baseEnd_843243 : Nat := 384879082257199592519557

theorem tailTrace_843243 : CollatzResearch.WordTrace tailWord_843243 prefixEnd_843243 384879082257199592519557 := by
  unfold tailWord_843243
  simp only [CollatzResearch.WordTrace]
  refine ⟨30755598884082100283934383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20503732589388066855956255 30755598884082100283934383)
  ·
    refine ⟨46133398326123150425901575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30755598884082100283934383 46133398326123150425901575)
    ·
      refine ⟨69200097489184725638852363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46133398326123150425901575 69200097489184725638852363)
      ·
        refine ⟨103800146233777088458278545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69200097489184725638852363 103800146233777088458278545)
        ·
          refine ⟨77850109675332816343708909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103800146233777088458278545 77850109675332816343708909)
          ·
            refine ⟨29193791128249806128890841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77850109675332816343708909 29193791128249806128890841)
            ·
              refine ⟨21895343346187354596668131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29193791128249806128890841 21895343346187354596668131)
              ·
                refine ⟨32843015019281031895002197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21895343346187354596668131 32843015019281031895002197)
                ·
                  refine ⟨384879082257199592519557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32843015019281031895002197 384879082257199592519557)
                  ·
                    rfl

theorem cell20_843243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_843243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843243 prefixEnd_843243 := by exact prefixLift 843243
  have htrace : WordTrace (prefixWord ++ tailWord_843243) baseStart_843243 baseEnd_843243 := by
    simpa [prefixWord, tailWord_843243, baseEnd_843243] using wordTrace_append hprefix tailTrace_843243
  have hstable : (prefixWord ++ tailWord_843243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843243).length < 2 ^ (prefixWord ++ tailWord_843243).sum := by decide
  have hdescent : baseEnd_843243 < baseStart_843243 := by decide
  rcases family_descends (prefixWord ++ tailWord_843243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843256 : List Nat := [2, 1, 2, 1, 1, 5, 4, 2, 2]
def baseStart_843256 : Nat := 118140960795 + 843256 * 2 ^ 59
def prefixEnd_843256 : Nat := 4983230072969 + 3 ^ 40 * 843256 * 2
def baseEnd_843256 : Nat := 384885015811429325086171

theorem tailTrace_843256 : CollatzResearch.WordTrace tailWord_843256 prefixEnd_843256 384885015811429325086171 := by
  unfold tailWord_843256
  simp only [CollatzResearch.WordTrace]
  refine ⟨15378036516517501752078811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20504048688690002336105081 15378036516517501752078811)
  ·
    refine ⟨23067054774776252628118217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15378036516517501752078811 23067054774776252628118217)
    ·
      refine ⟨17300291081082189471088663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23067054774776252628118217 17300291081082189471088663)
      ·
        refine ⟨25950436621623284206632995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17300291081082189471088663 25950436621623284206632995)
        ·
          refine ⟨38925654932434926309949493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25950436621623284206632995 38925654932434926309949493)
          ·
            refine ⟨3649280149915774341557765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38925654932434926309949493 3649280149915774341557765)
            ·
              refine ⟨684240028109207689042081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3649280149915774341557765 684240028109207689042081)
              ·
                refine ⟨513180021081905766781561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684240028109207689042081 513180021081905766781561)
                ·
                  refine ⟨384885015811429325086171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513180021081905766781561 384885015811429325086171)
                  ·
                    rfl

theorem cell20_843256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_843256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843256 prefixEnd_843256 := by exact prefixLift 843256
  have htrace : WordTrace (prefixWord ++ tailWord_843256) baseStart_843256 baseEnd_843256 := by
    simpa [prefixWord, tailWord_843256, baseEnd_843256] using wordTrace_append hprefix tailTrace_843256
  have hstable : (prefixWord ++ tailWord_843256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843256).length < 2 ^ (prefixWord ++ tailWord_843256).sum := by decide
  have hdescent : baseEnd_843256 < baseStart_843256 := by decide
  rcases family_descends (prefixWord ++ tailWord_843256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843304 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 3]
def baseStart_843304 : Nat := 118140960795 + 843304 * 2 ^ 59
def prefixEnd_843304 : Nat := 4983230072969 + 3 ^ 40 * 843304 * 2
def baseEnd_843304 : Nat := 384906924319354491485975

theorem tailTrace_843304 : CollatzResearch.WordTrace tailWord_843304 prefixEnd_843304 384906924319354491485975 := by
  unfold tailWord_843304
  simp only [CollatzResearch.WordTrace]
  refine ⟨15378911868430553850952483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20505215824574071801269977 15378911868430553850952483)
  ·
    refine ⟨23068367802645830776428725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15378911868430553850952483 23068367802645830776428725)
    ·
      refine ⟨2162659481498046635290193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23068367802645830776428725 2162659481498046635290193)
      ·
        refine ⟨1621994611123534976467645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2162659481498046635290193 1621994611123534976467645)
        ·
          refine ⟨608247979171325616175367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1621994611123534976467645 608247979171325616175367)
          ·
            refine ⟨912371968756988424263051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608247979171325616175367 912371968756988424263051)
            ·
              refine ⟨1368557953135482636394577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912371968756988424263051 1368557953135482636394577)
              ·
                refine ⟨1026418464851611977295933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368557953135482636394577 1026418464851611977295933)
                ·
                  refine ⟨384906924319354491485975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026418464851611977295933 384906924319354491485975)
                  ·
                    rfl

theorem cell20_843304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_843304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843304 prefixEnd_843304 := by exact prefixLift 843304
  have htrace : WordTrace (prefixWord ++ tailWord_843304) baseStart_843304 baseEnd_843304 := by
    simpa [prefixWord, tailWord_843304, baseEnd_843304] using wordTrace_append hprefix tailTrace_843304
  have hstable : (prefixWord ++ tailWord_843304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843304).length < 2 ^ (prefixWord ++ tailWord_843304).sum := by decide
  have hdescent : baseEnd_843304 < baseStart_843304 := by decide
  rcases family_descends (prefixWord ++ tailWord_843304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843315 : List Nat := [1, 1, 1, 2, 4, 3, 2, 4, 2]
def baseStart_843315 : Nat := 118140960795 + 843315 * 2 ^ 59
def prefixEnd_843315 : Nat := 4983230072969 + 3 ^ 40 * 843315 * 2
def baseEnd_843315 : Nat := 384911945019087342119263

theorem tailTrace_843315 : CollatzResearch.WordTrace tailWord_843315 prefixEnd_843315 384911945019087342119263 := by
  unfold tailWord_843315
  simp only [CollatzResearch.WordTrace]
  refine ⟨30758224939821256580555399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20505483293214171053703599 30758224939821256580555399)
  ·
    refine ⟨46137337409731884870833099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30758224939821256580555399 46137337409731884870833099)
    ·
      refine ⟨69206006114597827306249649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46137337409731884870833099 69206006114597827306249649)
      ·
        refine ⟨51904504585948370479687237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69206006114597827306249649 51904504585948370479687237)
        ·
          refine ⟨9732094609865319464941357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51904504585948370479687237 9732094609865319464941357)
          ·
            refine ⟨3649535478699494799353009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9732094609865319464941357 3649535478699494799353009)
            ·
              refine ⟨2737151609024621099514757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3649535478699494799353009 2737151609024621099514757)
              ·
                refine ⟨513215926692116456159017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2737151609024621099514757 513215926692116456159017)
                ·
                  refine ⟨384911945019087342119263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513215926692116456159017 384911945019087342119263)
                  ·
                    rfl

theorem cell20_843315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 2].length) (baseStart_843315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843315 prefixEnd_843315 := by exact prefixLift 843315
  have htrace : WordTrace (prefixWord ++ tailWord_843315) baseStart_843315 baseEnd_843315 := by
    simpa [prefixWord, tailWord_843315, baseEnd_843315] using wordTrace_append hprefix tailTrace_843315
  have hstable : (prefixWord ++ tailWord_843315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843315).length < 2 ^ (prefixWord ++ tailWord_843315).sum := by decide
  have hdescent : baseEnd_843315 < baseStart_843315 := by decide
  rcases family_descends (prefixWord ++ tailWord_843315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843325 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 3]
def baseStart_843325 : Nat := 118140960795 + 843325 * 2 ^ 59
def prefixEnd_843325 : Nat := 4983230072969 + 3 ^ 40 * 843325 * 2
def baseEnd_843325 : Nat := 384916509291571751785889

theorem tailTrace_843325 : CollatzResearch.WordTrace tailWord_843325 prefixEnd_843325 384916509291571751785889 := by
  unfold tailWord_843325
  simp only [CollatzResearch.WordTrace]
  refine ⟨30758589669785028288419429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20505726446523352192279619 30758589669785028288419429)
  ·
    refine ⟨5767235563084692804078643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30758589669785028288419429 5767235563084692804078643)
    ·
      refine ⟨8650853344627039206117965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5767235563084692804078643 8650853344627039206117965)
      ·
        refine ⟨3244070004235139702294237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8650853344627039206117965 3244070004235139702294237)
        ·
          refine ⟨1216526251588177388360339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3244070004235139702294237 1216526251588177388360339)
          ·
            refine ⟨1824789377382266082540509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216526251588177388360339 1824789377382266082540509)
            ·
              refine ⟨684296016518349780952691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1824789377382266082540509 684296016518349780952691)
              ·
                refine ⟨1026444024777524671429037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684296016518349780952691 1026444024777524671429037)
                ·
                  refine ⟨384916509291571751785889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026444024777524671429037 384916509291571751785889)
                  ·
                    rfl

theorem cell20_843325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_843325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843325 prefixEnd_843325 := by exact prefixLift 843325
  have htrace : WordTrace (prefixWord ++ tailWord_843325) baseStart_843325 baseEnd_843325 := by
    simpa [prefixWord, tailWord_843325, baseEnd_843325] using wordTrace_append hprefix tailTrace_843325
  have hstable : (prefixWord ++ tailWord_843325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843325).length < 2 ^ (prefixWord ++ tailWord_843325).sum := by decide
  have hdescent : baseEnd_843325 < baseStart_843325 := by decide
  rcases family_descends (prefixWord ++ tailWord_843325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843395 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_843395 : Nat := 118140960795 + 843395 * 2 ^ 59
def prefixEnd_843395 : Nat := 4983230072969 + 3 ^ 40 * 843395 * 2
def baseEnd_843395 : Nat := 384948459198962619452269

theorem tailTrace_843395 : CollatzResearch.WordTrace tailWord_843395 prefixEnd_843395 384948459198962619452269 := by
  unfold tailWord_843395
  simp only [CollatzResearch.WordTrace]
  refine ⟨30761142779531430243467639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20507428519687620162311759 30761142779531430243467639)
  ·
    refine ⟨46141714169297145365201459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30761142779531430243467639 46141714169297145365201459)
    ·
      refine ⟨69212571253945718047802189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46141714169297145365201459 69212571253945718047802189)
      ·
        refine ⟨25954714220229644267925821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69212571253945718047802189 25954714220229644267925821)
        ·
          refine ⟨9733017832586116600472183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25954714220229644267925821 9733017832586116600472183)
          ·
            refine ⟨14599526748879174900708275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9733017832586116600472183 14599526748879174900708275)
            ·
              refine ⟨21899290123318762351062413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14599526748879174900708275 21899290123318762351062413)
              ·
                refine ⟨8212233796244535881648405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21899290123318762351062413 8212233796244535881648405)
                ·
                  refine ⟨384948459198962619452269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8212233796244535881648405 384948459198962619452269)
                  ·
                    rfl

theorem cell20_843395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_843395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843395 prefixEnd_843395 := by exact prefixLift 843395
  have htrace : WordTrace (prefixWord ++ tailWord_843395) baseStart_843395 baseEnd_843395 := by
    simpa [prefixWord, tailWord_843395, baseEnd_843395] using wordTrace_append hprefix tailTrace_843395
  have hstable : (prefixWord ++ tailWord_843395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843395).length < 2 ^ (prefixWord ++ tailWord_843395).sum := by decide
  have hdescent : baseEnd_843395 < baseStart_843395 := by decide
  rcases family_descends (prefixWord ++ tailWord_843395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843422 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_843422 : Nat := 118140960795 + 843422 * 2 ^ 59
def prefixEnd_843422 : Nat := 4983230072969 + 3 ^ 40 * 843422 * 2
def baseEnd_843422 : Nat := 384960782734670525552159

theorem tailTrace_843422 : CollatzResearch.WordTrace tailWord_843422 prefixEnd_843422 384960782734670525552159 := by
  unfold tailWord_843422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845265943804201731837565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20508085033622409236467013 3845265943804201731837565)
  ·
    refine ⟨1441974728926575649439087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3845265943804201731837565 1441974728926575649439087)
    ·
      refine ⟨2162962093389863474158631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441974728926575649439087 2162962093389863474158631)
      ·
        refine ⟨3244443140084795211237947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162962093389863474158631 3244443140084795211237947)
        ·
          refine ⟨4866664710127192816856921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244443140084795211237947 4866664710127192816856921)
          ·
            refine ⟨3649998532595394612642691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4866664710127192816856921 3649998532595394612642691)
            ·
              refine ⟨5474997798893091918964037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649998532595394612642691 5474997798893091918964037)
              ·
                refine ⟨1026562087292454734805757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5474997798893091918964037 1026562087292454734805757)
                ·
                  refine ⟨384960782734670525552159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026562087292454734805757 384960782734670525552159)
                  ·
                    rfl

theorem cell20_843422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_843422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843422 prefixEnd_843422 := by exact prefixLift 843422
  have htrace : WordTrace (prefixWord ++ tailWord_843422) baseStart_843422 baseEnd_843422 := by
    simpa [prefixWord, tailWord_843422, baseEnd_843422] using wordTrace_append hprefix tailTrace_843422
  have hstable : (prefixWord ++ tailWord_843422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843422).length < 2 ^ (prefixWord ++ tailWord_843422).sum := by decide
  have hdescent : baseEnd_843422 < baseStart_843422 := by decide
  rcases family_descends (prefixWord ++ tailWord_843422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843425 : List Nat := [1, 2, 3, 3, 2, 3, 2, 2, 2]
def baseStart_843425 : Nat := 118140960795 + 843425 * 2 ^ 59
def prefixEnd_843425 : Nat := 4983230072969 + 3 ^ 40 * 843425 * 2
def baseEnd_843425 : Nat := 384962152016415848452147

theorem tailTrace_843425 : CollatzResearch.WordTrace tailWord_843425 prefixEnd_843425 384962152016415848452147 := by
  unfold tailWord_843425
  simp only [CollatzResearch.WordTrace]
  refine ⟨30762236969422745367059729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20508157979615163578039819 30762236969422745367059729)
  ·
    refine ⟨23071677727067059025294797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30762236969422745367059729 23071677727067059025294797)
    ·
      refine ⟨8651879147650147134485549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23071677727067059025294797 8651879147650147134485549)
      ·
        refine ⟨3244454680368805175432081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8651879147650147134485549 3244454680368805175432081)
        ·
          refine ⟨2433341010276603881574061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244454680368805175432081 2433341010276603881574061)
          ·
            refine ⟨912502878853726455590273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2433341010276603881574061 912502878853726455590273)
            ·
              refine ⟨684377159140294841692705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912502878853726455590273 684377159140294841692705)
              ·
                refine ⟨513282869355221131269529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684377159140294841692705 513282869355221131269529)
                ·
                  refine ⟨384962152016415848452147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513282869355221131269529 384962152016415848452147)
                  ·
                    rfl

theorem cell20_843425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_843425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843425 prefixEnd_843425 := by exact prefixLift 843425
  have htrace : WordTrace (prefixWord ++ tailWord_843425) baseStart_843425 baseEnd_843425 := by
    simpa [prefixWord, tailWord_843425, baseEnd_843425] using wordTrace_append hprefix tailTrace_843425
  have hstable : (prefixWord ++ tailWord_843425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843425).length < 2 ^ (prefixWord ++ tailWord_843425).sum := by decide
  have hdescent : baseEnd_843425 < baseStart_843425 := by decide
  rcases family_descends (prefixWord ++ tailWord_843425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843446 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_843446 : Nat := 118140960795 + 843446 * 2 ^ 59
def prefixEnd_843446 : Nat := 4983230072969 + 3 ^ 40 * 843446 * 2
def baseEnd_843446 : Nat := 384971736988633108752061

theorem tailTrace_843446 : CollatzResearch.WordTrace tailWord_843446 prefixEnd_843446 384971736988633108752061 := by
  unfold tailWord_843446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922687681396666622098387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20508668601564443969049461 1922687681396666622098387)
  ·
    refine ⟨2884031522094999933147581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1922687681396666622098387 2884031522094999933147581)
    ·
      refine ⟨1081511820785624974930343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2884031522094999933147581 1081511820785624974930343)
      ·
        refine ⟨1622267731178437462395515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081511820785624974930343 1622267731178437462395515)
        ·
          refine ⟨2433401596767656193593273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622267731178437462395515 2433401596767656193593273)
          ·
            refine ⟨1825051197575742145194955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2433401596767656193593273 1825051197575742145194955)
            ·
              refine ⟨2737576796363613217792433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825051197575742145194955 2737576796363613217792433)
              ·
                refine ⟨2053182597272709913344325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2737576796363613217792433 2053182597272709913344325)
                ·
                  refine ⟨384971736988633108752061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2053182597272709913344325 384971736988633108752061)
                  ·
                    rfl

theorem cell20_843446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_843446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843446 prefixEnd_843446 := by exact prefixLift 843446
  have htrace : WordTrace (prefixWord ++ tailWord_843446) baseStart_843446 baseEnd_843446 := by
    simpa [prefixWord, tailWord_843446, baseEnd_843446] using wordTrace_append hprefix tailTrace_843446
  have hstable : (prefixWord ++ tailWord_843446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843446).length < 2 ^ (prefixWord ++ tailWord_843446).sum := by decide
  have hdescent : baseEnd_843446 < baseStart_843446 := by decide
  rcases family_descends (prefixWord ++ tailWord_843446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843450 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_843450 : Nat := 118140960795 + 843450 * 2 ^ 59
def prefixEnd_843450 : Nat := 4983230072969 + 3 ^ 40 * 843450 * 2
def baseEnd_843450 : Nat := 384973562697626872618711

theorem tailTrace_843450 : CollatzResearch.WordTrace tailWord_843450 prefixEnd_843450 384973562697626872618711 := by
  unfold tailWord_843450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7690787198583043659179951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20508765862888116424479869 7690787198583043659179951)
  ·
    refine ⟨11536180797874565488769927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7690787198583043659179951 11536180797874565488769927)
    ·
      refine ⟨17304271196811848233154891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11536180797874565488769927 17304271196811848233154891)
      ·
        refine ⟨25956406795217772349732337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17304271196811848233154891 25956406795217772349732337)
        ·
          refine ⟨19467305096413329262299253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25956406795217772349732337 19467305096413329262299253)
          ·
            refine ⟨1825059852788749618340555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19467305096413329262299253 1825059852788749618340555)
            ·
              refine ⟨2737589779183124427510833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825059852788749618340555 2737589779183124427510833)
              ·
                refine ⟨2053192334387343320633125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2737589779183124427510833 2053192334387343320633125)
                ·
                  refine ⟨384973562697626872618711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2053192334387343320633125 384973562697626872618711)
                  ·
                    rfl

theorem cell20_843450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_843450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843450 prefixEnd_843450 := by exact prefixLift 843450
  have htrace : WordTrace (prefixWord ++ tailWord_843450) baseStart_843450 baseEnd_843450 := by
    simpa [prefixWord, tailWord_843450, baseEnd_843450] using wordTrace_append hprefix tailTrace_843450
  have hstable : (prefixWord ++ tailWord_843450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843450).length < 2 ^ (prefixWord ++ tailWord_843450).sum := by decide
  have hdescent : baseEnd_843450 < baseStart_843450 := by decide
  rcases family_descends (prefixWord ++ tailWord_843450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843464 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_843464 : Nat := 118140960795 + 843464 * 2 ^ 59
def prefixEnd_843464 : Nat := 4983230072969 + 3 ^ 40 * 843464 * 2
def baseEnd_843464 : Nat := 384979952679105046151987

theorem tailTrace_843464 : CollatzResearch.WordTrace tailWord_843464 prefixEnd_843464 384979952679105046151987 := by
  unfold tailWord_843464
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381829708140727513864723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20509106277520970018486297 15381829708140727513864723)
  ·
    refine ⟨23072744562211091270797085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15381829708140727513864723 23072744562211091270797085)
    ·
      refine ⟨8652279210829159226548907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23072744562211091270797085 8652279210829159226548907)
      ·
        refine ⟨12978418816243738839823361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8652279210829159226548907 12978418816243738839823361)
        ·
          refine ⟨9733814112182804129867521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12978418816243738839823361 9733814112182804129867521)
          ·
            refine ⟨7300360584137103097400641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9733814112182804129867521 7300360584137103097400641)
            ·
              refine ⟨5475270438102827323050481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7300360584137103097400641 5475270438102827323050481)
              ·
                refine ⟨4106452828577120492287861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5475270438102827323050481 4106452828577120492287861)
                ·
                  refine ⟨384979952679105046151987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4106452828577120492287861 384979952679105046151987)
                  ·
                    rfl

theorem cell20_843464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_843464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843464 prefixEnd_843464 := by exact prefixLift 843464
  have htrace : WordTrace (prefixWord ++ tailWord_843464) baseStart_843464 baseEnd_843464 := by
    simpa [prefixWord, tailWord_843464, baseEnd_843464] using wordTrace_append hprefix tailTrace_843464
  have hstable : (prefixWord ++ tailWord_843464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843464).length < 2 ^ (prefixWord ++ tailWord_843464).sum := by decide
  have hdescent : baseEnd_843464 < baseStart_843464 := by decide
  rcases family_descends (prefixWord ++ tailWord_843464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843481 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 3]
def baseStart_843481 : Nat := 118140960795 + 843481 * 2 ^ 59
def prefixEnd_843481 : Nat := 4983230072969 + 3 ^ 40 * 843481 * 2
def baseEnd_843481 : Nat := 384987711942328542585251

theorem tailTrace_843481 : CollatzResearch.WordTrace tailWord_843481 prefixEnd_843481 384987711942328542585251 := by
  unfold tailWord_843481
  simp only [CollatzResearch.WordTrace]
  refine ⟨30764279457219866931098297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20509519638146577954065531 30764279457219866931098297)
  ·
    refine ⟨23073209592914900198323723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30764279457219866931098297 23073209592914900198323723)
    ·
      refine ⟨34609814389372350297485585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23073209592914900198323723 34609814389372350297485585)
      ·
        refine ⟨25957360792029262723114189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34609814389372350297485585 25957360792029262723114189)
        ·
          refine ⟨9734010297010973521167821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25957360792029262723114189 9734010297010973521167821)
          ·
            refine ⟨3650253861379115070437933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9734010297010973521167821 3650253861379115070437933)
            ·
              refine ⟨1368845198017168151414225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3650253861379115070437933 1368845198017168151414225)
              ·
                refine ⟨1026633898512876113560669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368845198017168151414225 1026633898512876113560669)
                ·
                  refine ⟨384987711942328542585251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026633898512876113560669 384987711942328542585251)
                  ·
                    rfl

theorem cell20_843481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_843481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843481 prefixEnd_843481 := by exact prefixLift 843481
  have htrace : WordTrace (prefixWord ++ tailWord_843481) baseStart_843481 baseEnd_843481 := by
    simpa [prefixWord, tailWord_843481, baseEnd_843481] using wordTrace_append hprefix tailTrace_843481
  have hstable : (prefixWord ++ tailWord_843481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843481).length < 2 ^ (prefixWord ++ tailWord_843481).sum := by decide
  have hdescent : baseEnd_843481 < baseStart_843481 := by decide
  rcases family_descends (prefixWord ++ tailWord_843481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843484 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_843484 : Nat := 118140960795 + 843484 * 2 ^ 59
def prefixEnd_843484 : Nat := 4983230072969 + 3 ^ 40 * 843484 * 2
def baseEnd_843484 : Nat := 384989081224073865485239

theorem tailTrace_843484 : CollatzResearch.WordTrace tailWord_843484 prefixEnd_843484 384989081224073865485239 := by
  unfold tailWord_843484
  simp only [CollatzResearch.WordTrace]
  refine ⟨15382194438104499221728753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20509592584139332295638337 15382194438104499221728753)
  ·
    refine ⟨11536645828578374416296565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15382194438104499221728753 11536645828578374416296565)
    ·
      refine ⟨1081560546429222601527803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11536645828578374416296565 1081560546429222601527803)
      ·
        refine ⟨1622340819643833902291705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081560546429222601527803 1622340819643833902291705)
        ·
          refine ⟨1216755614732875426718779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622340819643833902291705 1216755614732875426718779)
          ·
            refine ⟨1825133422099313140078169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216755614732875426718779 1825133422099313140078169)
            ·
              refine ⟨1368850066574484855058627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1825133422099313140078169 1368850066574484855058627)
              ·
                refine ⟨2053275099861727282587941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368850066574484855058627 2053275099861727282587941)
                ·
                  refine ⟨384989081224073865485239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2053275099861727282587941 384989081224073865485239)
                  ·
                    rfl

theorem cell20_843484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_843484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843484 prefixEnd_843484 := by exact prefixLift 843484
  have htrace : WordTrace (prefixWord ++ tailWord_843484) baseStart_843484 baseEnd_843484 := by
    simpa [prefixWord, tailWord_843484, baseEnd_843484] using wordTrace_append hprefix tailTrace_843484
  have hstable : (prefixWord ++ tailWord_843484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843484).length < 2 ^ (prefixWord ++ tailWord_843484).sum := by decide
  have hdescent : baseEnd_843484 < baseStart_843484 := by decide
  rcases family_descends (prefixWord ++ tailWord_843484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843508 : List Nat := [2, 6, 1, 1, 1, 1, 4, 4]
def baseStart_843508 : Nat := 118140960795 + 843508 * 2 ^ 59
def prefixEnd_843508 : Nat := 4983230072969 + 3 ^ 40 * 843508 * 2
def baseEnd_843508 : Nat := 128333345159345482895047

theorem tailTrace_843508 : CollatzResearch.WordTrace tailWord_843508 prefixEnd_843508 128333345159345482895047 := by
  unfold tailWord_843508
  simp only [CollatzResearch.WordTrace]
  refine ⟨15382632114061025271165589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20510176152081367028220785 15382632114061025271165589)
  ·
    refine ⟨721060880346610559585887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15382632114061025271165589 721060880346610559585887)
    ·
      refine ⟨1081591320519915839378831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 721060880346610559585887 1081591320519915839378831)
      ·
        refine ⟨1622386980779873759068247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081591320519915839378831 1622386980779873759068247)
        ·
          refine ⟨2433580471169810638602371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1622386980779873759068247 2433580471169810638602371)
          ·
            refine ⟨3650370706754715957903557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433580471169810638602371 3650370706754715957903557)
            ·
              refine ⟨684444507516509242106917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3650370706754715957903557 684444507516509242106917)
              ·
                refine ⟨128333345159345482895047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684444507516509242106917 128333345159345482895047)
                ·
                  rfl

theorem cell20_843508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_843508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843508 prefixEnd_843508 := by exact prefixLift 843508
  have htrace : WordTrace (prefixWord ++ tailWord_843508) baseStart_843508 baseEnd_843508 := by
    simpa [prefixWord, tailWord_843508, baseEnd_843508] using wordTrace_append hprefix tailTrace_843508
  have hstable : (prefixWord ++ tailWord_843508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843508).length < 2 ^ (prefixWord ++ tailWord_843508).sum := by decide
  have hdescent : baseEnd_843508 < baseStart_843508 := by decide
  rcases family_descends (prefixWord ++ tailWord_843508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843518 : List Nat := [4, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_843518 : Nat := 118140960795 + 843518 * 2 ^ 59
def prefixEnd_843518 : Nat := 4983230072969 + 3 ^ 40 * 843518 * 2
def baseEnd_843518 : Nat := 385004599750520858351767

theorem tailTrace_843518 : CollatzResearch.WordTrace tailWord_843518 prefixEnd_843518 385004599750520858351767 := by
  unfold tailWord_843518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845703619760727781274401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20510419305390548166796805 3845703619760727781274401)
  ·
    refine ⟨2884277714820545835955801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3845703619760727781274401 2884277714820545835955801)
    ·
      refine ⟨2163208286115409376966851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2884277714820545835955801 2163208286115409376966851)
      ·
        refine ⟨3244812429173114065450277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2163208286115409376966851 3244812429173114065450277)
        ·
          refine ⟨608402330469958887271927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3244812429173114065450277 608402330469958887271927)
          ·
            refine ⟨912603495704938330907891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608402330469958887271927 912603495704938330907891)
            ·
              refine ⟨1368905243557407496361837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912603495704938330907891 1368905243557407496361837)
              ·
                refine ⟨513339466334027811135689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1368905243557407496361837 513339466334027811135689)
                ·
                  refine ⟨385004599750520858351767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513339466334027811135689 385004599750520858351767)
                  ·
                    rfl

theorem cell20_843518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_843518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843518 prefixEnd_843518 := by exact prefixLift 843518
  have htrace : WordTrace (prefixWord ++ tailWord_843518) baseStart_843518 baseEnd_843518 := by
    simpa [prefixWord, tailWord_843518, baseEnd_843518] using wordTrace_append hprefix tailTrace_843518
  have hstable : (prefixWord ++ tailWord_843518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843518).length < 2 ^ (prefixWord ++ tailWord_843518).sum := by decide
  have hdescent : baseEnd_843518 < baseStart_843518 := by decide
  rcases family_descends (prefixWord ++ tailWord_843518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843543 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 4]
def baseStart_843543 : Nat := 118140960795 + 843543 * 2 ^ 59
def prefixEnd_843543 : Nat := 4983230072969 + 3 ^ 40 * 843543 * 2
def baseEnd_843543 : Nat := 385016010431731882518331

theorem tailTrace_843543 : CollatzResearch.WordTrace tailWord_843543 prefixEnd_843543 385016010431731882518331 := by
  unfold tailWord_843543
  simp only [CollatzResearch.WordTrace]
  refine ⟨30766540782995251519855283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20511027188663501013236855 30766540782995251519855283)
  ·
    refine ⟨46149811174492877279782925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30766540782995251519855283 46149811174492877279782925)
    ·
      refine ⟨17306179190434828979918597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46149811174492877279782925 17306179190434828979918597)
      ·
        refine ⟨3244908598206530433734737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17306179190434828979918597 3244908598206530433734737)
        ·
          refine ⟨2433681448654897825301053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244908598206530433734737 2433681448654897825301053)
          ·
            refine ⟨912630543245586684487895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2433681448654897825301053 912630543245586684487895)
            ·
              refine ⟨1368945814868380026731843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 912630543245586684487895 1368945814868380026731843)
              ·
                refine ⟨2053418722302570040097765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368945814868380026731843 2053418722302570040097765)
                ·
                  refine ⟨385016010431731882518331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2053418722302570040097765 385016010431731882518331)
                  ·
                    rfl

theorem cell20_843543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 4].length) (baseStart_843543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843543 prefixEnd_843543 := by exact prefixLift 843543
  have htrace : WordTrace (prefixWord ++ tailWord_843543) baseStart_843543 baseEnd_843543 := by
    simpa [prefixWord, tailWord_843543, baseEnd_843543] using wordTrace_append hprefix tailTrace_843543
  have hstable : (prefixWord ++ tailWord_843543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843543).length < 2 ^ (prefixWord ++ tailWord_843543).sum := by decide
  have hdescent : baseEnd_843543 < baseStart_843543 := by decide
  rcases family_descends (prefixWord ++ tailWord_843543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843557 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 3]
def baseStart_843557 : Nat := 118140960795 + 843557 * 2 ^ 59
def prefixEnd_843557 : Nat := 4983230072969 + 3 ^ 40 * 843557 * 2
def baseEnd_843557 : Nat := 385022400413210056051607

theorem tailTrace_843557 : CollatzResearch.WordTrace tailWord_843557 prefixEnd_843557 385022400413210056051607 := by
  unfold tailWord_843557
  simp only [CollatzResearch.WordTrace]
  refine ⟨30767051404944531910864925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20511367603296354607243283 30767051404944531910864925)
  ·
    refine ⟨11537644276854199466574347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30767051404944531910864925 11537644276854199466574347)
    ·
      refine ⟨17306466415281299199861521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11537644276854199466574347 17306466415281299199861521)
      ·
        refine ⟨12979849811460974399896141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17306466415281299199861521 12979849811460974399896141)
        ·
          refine ⟨4867443679297865399961053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12979849811460974399896141 4867443679297865399961053)
          ·
            refine ⟨1825291379736699524985395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4867443679297865399961053 1825291379736699524985395)
            ·
              refine ⟨2737937069605049287478093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825291379736699524985395 2737937069605049287478093)
              ·
                refine ⟨1026726401101893482804285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2737937069605049287478093 1026726401101893482804285)
                ·
                  refine ⟨385022400413210056051607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026726401101893482804285 385022400413210056051607)
                  ·
                    rfl

theorem cell20_843557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_843557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843557 prefixEnd_843557 := by exact prefixLift 843557
  have htrace : WordTrace (prefixWord ++ tailWord_843557) baseStart_843557 baseEnd_843557 := by
    simpa [prefixWord, tailWord_843557, baseEnd_843557] using wordTrace_append hprefix tailTrace_843557
  have hstable : (prefixWord ++ tailWord_843557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843557).length < 2 ^ (prefixWord ++ tailWord_843557).sum := by decide
  have hdescent : baseEnd_843557 < baseStart_843557 := by decide
  rcases family_descends (prefixWord ++ tailWord_843557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843592 : List Nat := [2, 1, 3, 1, 1, 12]
def baseStart_843592 : Nat := 118140960795 + 843592 * 2 ^ 59
def prefixEnd_843592 : Nat := 4983230072969 + 3 ^ 40 * 843592 * 2
def baseEnd_843592 : Nat := 14260680569144647773511

theorem tailTrace_843592 : CollatzResearch.WordTrace tailWord_843592 prefixEnd_843592 14260680569144647773511 := by
  unfold tailWord_843592
  simp only [CollatzResearch.WordTrace]
  refine ⟨15384163979908866444194515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20512218639878488592259353 15384163979908866444194515)
  ·
    refine ⟨23076245969863299666291773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15384163979908866444194515 23076245969863299666291773)
    ·
      refine ⟨8653592238698737374859415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23076245969863299666291773 8653592238698737374859415)
      ·
        refine ⟨12980388358048106062289123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8653592238698737374859415 12980388358048106062289123)
        ·
          refine ⟨19470582537072159093433685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12980388358048106062289123 19470582537072159093433685)
          ·
            refine ⟨14260680569144647773511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19470582537072159093433685 14260680569144647773511)
            ·
              rfl

theorem cell20_843592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 12].length) (baseStart_843592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843592 prefixEnd_843592 := by exact prefixLift 843592
  have htrace : WordTrace (prefixWord ++ tailWord_843592) baseStart_843592 baseEnd_843592 := by
    simpa [prefixWord, tailWord_843592, baseEnd_843592] using wordTrace_append hprefix tailTrace_843592
  have hstable : (prefixWord ++ tailWord_843592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843592).length < 2 ^ (prefixWord ++ tailWord_843592).sum := by decide
  have hdescent : baseEnd_843592 < baseStart_843592 := by decide
  rcases family_descends (prefixWord ++ tailWord_843592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843681 : List Nat := [1, 2, 3, 4, 2, 2, 2, 4]
def baseStart_843681 : Nat := 118140960795 + 843681 * 2 ^ 59
def prefixEnd_843681 : Nat := 4983230072969 + 3 ^ 40 * 843681 * 2
def baseEnd_843681 : Nat := 128359665797338911972589

theorem tailTrace_843681 : CollatzResearch.WordTrace tailWord_843681 prefixEnd_843681 128359665797338911972589 := by
  unfold tailWord_843681
  simp only [CollatzResearch.WordTrace]
  refine ⟨30771574056495301088378897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20514382704330200725585931 30771574056495301088378897)
  ·
    refine ⟨23078680542371475816284173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30771574056495301088378897 23078680542371475816284173)
    ·
      refine ⟨8654505203389303431106565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23078680542371475816284173 8654505203389303431106565)
      ·
        refine ⟨1622719725635494393332481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8654505203389303431106565 1622719725635494393332481)
        ·
          refine ⟨1217039794226620794999361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622719725635494393332481 1217039794226620794999361)
          ·
            refine ⟨912779845669965596249521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1217039794226620794999361 912779845669965596249521)
            ·
              refine ⟨684584884252474197187141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912779845669965596249521 684584884252474197187141)
              ·
                refine ⟨128359665797338911972589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684584884252474197187141 128359665797338911972589)
                ·
                  rfl

theorem cell20_843681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 4].length) (baseStart_843681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843681 prefixEnd_843681 := by exact prefixLift 843681
  have htrace : WordTrace (prefixWord ++ tailWord_843681) baseStart_843681 baseEnd_843681 := by
    simpa [prefixWord, tailWord_843681, baseEnd_843681] using wordTrace_append hprefix tailTrace_843681
  have hstable : (prefixWord ++ tailWord_843681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843681).length < 2 ^ (prefixWord ++ tailWord_843681).sum := by decide
  have hdescent : baseEnd_843681 < baseStart_843681 := by decide
  rcases family_descends (prefixWord ++ tailWord_843681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843761 : List Nat := [1, 2, 2, 2, 6, 7]
def baseStart_843761 : Nat := 118140960795 + 843761 * 2 ^ 59
def prefixEnd_843761 : Nat := 4983230072969 + 3 ^ 40 * 843761 * 2
def baseEnd_843761 : Nat := 14263537465625630120399

theorem tailTrace_843761 : CollatzResearch.WordTrace tailWord_843761 prefixEnd_843761 14263537465625630120399 := by
  unfold tailWord_843761
  simp only [CollatzResearch.WordTrace]
  refine ⟨30774491896205474751291137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20516327930803649834194091 30774491896205474751291137)
  ·
    refine ⟨23080868922154106063468353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30774491896205474751291137 23080868922154106063468353)
    ·
      refine ⟨17310651691615579547601265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23080868922154106063468353 17310651691615579547601265)
      ·
        refine ⟨12982988768711684660700949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17310651691615579547601265 12982988768711684660700949)
        ·
          refine ⟨608577598533360218470357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12982988768711684660700949 608577598533360218470357)
          ·
            refine ⟨14263537465625630120399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 608577598533360218470357 14263537465625630120399)
            ·
              rfl

theorem cell20_843761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 7].length) (baseStart_843761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843761 prefixEnd_843761 := by exact prefixLift 843761
  have htrace : WordTrace (prefixWord ++ tailWord_843761) baseStart_843761 baseEnd_843761 := by
    simpa [prefixWord, tailWord_843761, baseEnd_843761] using wordTrace_append hprefix tailTrace_843761
  have hstable : (prefixWord ++ tailWord_843761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843761).length < 2 ^ (prefixWord ++ tailWord_843761).sum := by decide
  have hdescent : baseEnd_843761 < baseStart_843761 := by decide
  rcases family_descends (prefixWord ++ tailWord_843761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843768 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 3]
def baseStart_843768 : Nat := 118140960795 + 843768 * 2 ^ 59
def prefixEnd_843768 : Nat := 4983230072969 + 3 ^ 40 * 843768 * 2
def baseEnd_843768 : Nat := 385118706562631100017411

theorem tailTrace_843768 : CollatzResearch.WordTrace tailWord_843768 prefixEnd_843768 385118706562631100017411 := by
  unfold tailWord_843768
  simp only [CollatzResearch.WordTrace]
  refine ⟨15387373603590057473397979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20516498138120076631197305 15387373603590057473397979)
  ·
    refine ⟨23081060405385086210096969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15387373603590057473397979 23081060405385086210096969)
    ·
      refine ⟨17310795304038814657572727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23081060405385086210096969 17310795304038814657572727)
      ·
        refine ⟨25966192956058221986359091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17310795304038814657572727 25966192956058221986359091)
        ·
          refine ⟨38949289434087332979538637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25966192956058221986359091 38949289434087332979538637)
          ·
            refine ⟨14605983537782749867326989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38949289434087332979538637 14605983537782749867326989)
            ·
              refine ⟨5477243826668531200247621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14605983537782749867326989 5477243826668531200247621)
              ·
                refine ⟨1026983217500349600046429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5477243826668531200247621 1026983217500349600046429)
                ·
                  refine ⟨385118706562631100017411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026983217500349600046429 385118706562631100017411)
                  ·
                    rfl

theorem cell20_843768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_843768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843768 prefixEnd_843768 := by exact prefixLift 843768
  have htrace : WordTrace (prefixWord ++ tailWord_843768) baseStart_843768 baseEnd_843768 := by
    simpa [prefixWord, tailWord_843768, baseEnd_843768] using wordTrace_append hprefix tailTrace_843768
  have hstable : (prefixWord ++ tailWord_843768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843768).length < 2 ^ (prefixWord ++ tailWord_843768).sum := by decide
  have hdescent : baseEnd_843768 < baseStart_843768 := by decide
  rcases family_descends (prefixWord ++ tailWord_843768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843771 : List Nat := [1, 1, 1, 1, 1, 3, 8, 2, 2]
def baseStart_843771 : Nat := 118140960795 + 843771 * 2 ^ 59
def prefixEnd_843771 : Nat := 4983230072969 + 3 ^ 40 * 843771 * 2
def baseEnd_843771 : Nat := 385120075844376422917399

theorem tailTrace_843771 : CollatzResearch.WordTrace tailWord_843771 prefixEnd_843771 385120075844376422917399 := by
  unfold tailWord_843771
  simp only [CollatzResearch.WordTrace]
  refine ⟨30774856626169246459155167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20516571084112830972770111 30774856626169246459155167)
  ·
    refine ⟨46162284939253869688732751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30774856626169246459155167 46162284939253869688732751)
    ·
      refine ⟨69243427408880804533099127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46162284939253869688732751 69243427408880804533099127)
      ·
        refine ⟨103865141113321206799648691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69243427408880804533099127 103865141113321206799648691)
        ·
          refine ⟨155797711669981810199473037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103865141113321206799648691 155797711669981810199473037)
          ·
            refine ⟨58424141876243178824802389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155797711669981810199473037 58424141876243178824802389)
            ·
              refine ⟨684657912612224751853153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 58424141876243178824802389 684657912612224751853153)
              ·
                refine ⟨513493434459168563889865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684657912612224751853153 513493434459168563889865)
                ·
                  refine ⟨385120075844376422917399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513493434459168563889865 385120075844376422917399)
                  ·
                    rfl

theorem cell20_843771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 2].length) (baseStart_843771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843771 prefixEnd_843771 := by exact prefixLift 843771
  have htrace : WordTrace (prefixWord ++ tailWord_843771) baseStart_843771 baseEnd_843771 := by
    simpa [prefixWord, tailWord_843771, baseEnd_843771] using wordTrace_append hprefix tailTrace_843771
  have hstable : (prefixWord ++ tailWord_843771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843771).length < 2 ^ (prefixWord ++ tailWord_843771).sum := by decide
  have hdescent : baseEnd_843771 < baseStart_843771 := by decide
  rcases family_descends (prefixWord ++ tailWord_843771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843816 : List Nat := [2, 1, 5, 3, 1, 1, 7]
def baseStart_843816 : Nat := 118140960795 + 843816 * 2 ^ 59
def prefixEnd_843816 : Nat := 4983230072969 + 3 ^ 40 * 843816 * 2
def baseEnd_843816 : Nat := 42793401674506251824135

theorem tailTrace_843816 : CollatzResearch.WordTrace tailWord_843816 prefixEnd_843816 42793401674506251824135 := by
  unfold tailWord_843816
  simp only [CollatzResearch.WordTrace]
  refine ⟨15388248955503109572271651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20517665274004146096362201 15388248955503109572271651)
  ·
    refine ⟨23082373433254664358407477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15388248955503109572271651 23082373433254664358407477)
    ·
      refine ⟨2163972509367624783600701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23082373433254664358407477 2163972509367624783600701)
      ·
        refine ⟨811489691012859293850263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2163972509367624783600701 811489691012859293850263)
        ·
          refine ⟨1217234536519288940775395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811489691012859293850263 1217234536519288940775395)
          ·
            refine ⟨1825851804778933411163093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217234536519288940775395 1825851804778933411163093)
            ·
              refine ⟨42793401674506251824135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1825851804778933411163093 42793401674506251824135)
              ·
                rfl

theorem cell20_843816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 7].length) (baseStart_843816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843816 prefixEnd_843816 := by exact prefixLift 843816
  have htrace : WordTrace (prefixWord ++ tailWord_843816) baseStart_843816 baseEnd_843816 := by
    simpa [prefixWord, tailWord_843816, baseEnd_843816] using wordTrace_append hprefix tailTrace_843816
  have hstable : (prefixWord ++ tailWord_843816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843816).length < 2 ^ (prefixWord ++ tailWord_843816).sum := by decide
  have hdescent : baseEnd_843816 < baseStart_843816 := by decide
  rcases family_descends (prefixWord ++ tailWord_843816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843854 : List Nat := [4, 1, 1, 1, 1, 6, 2, 4]
def baseStart_843854 : Nat := 118140960795 + 843854 * 2 ^ 59
def prefixEnd_843854 : Nat := 4983230072969 + 3 ^ 40 * 843854 * 2
def baseEnd_843854 : Nat := 128385986435332341050131

theorem tailTrace_843854 : CollatzResearch.WordTrace tailWord_843854 prefixEnd_843854 128385986435332341050131 := by
  unfold tailWord_843854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3847235485608568954303327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20518589256579034422951077 3847235485608568954303327)
  ·
    refine ⟨5770853228412853431454991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3847235485608568954303327 5770853228412853431454991)
    ·
      refine ⟨8656279842619280147182487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5770853228412853431454991 8656279842619280147182487)
      ·
        refine ⟨12984419763928920220773731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8656279842619280147182487 12984419763928920220773731)
        ·
          refine ⟨19476629645893380331160597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12984419763928920220773731 19476629645893380331160597)
          ·
            refine ⟨912967014651252203023153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19476629645893380331160597 912967014651252203023153)
            ·
              refine ⟨684725260988439152267365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912967014651252203023153 684725260988439152267365)
              ·
                refine ⟨128385986435332341050131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684725260988439152267365 128385986435332341050131)
                ·
                  rfl

theorem cell20_843854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_843854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843854 prefixEnd_843854 := by exact prefixLift 843854
  have htrace : WordTrace (prefixWord ++ tailWord_843854) baseStart_843854 baseEnd_843854 := by
    simpa [prefixWord, tailWord_843854, baseEnd_843854] using wordTrace_append hprefix tailTrace_843854
  have hstable : (prefixWord ++ tailWord_843854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843854).length < 2 ^ (prefixWord ++ tailWord_843854).sum := by decide
  have hdescent : baseEnd_843854 < baseStart_843854 := by decide
  rcases family_descends (prefixWord ++ tailWord_843854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843865 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_843865 : Nat := 118140960795 + 843865 * 2 ^ 59
def prefixEnd_843865 : Nat := 4983230072969 + 3 ^ 40 * 843865 * 2
def baseEnd_843865 : Nat := 385162980005729873783681

theorem tailTrace_843865 : CollatzResearch.WordTrace tailWord_843865 prefixEnd_843865 385162980005729873783681 := by
  unfold tailWord_843865
  simp only [CollatzResearch.WordTrace]
  refine ⟨30778285087828700513077049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20518856725219133675384699 30778285087828700513077049)
  ·
    refine ⟨23083713815871525384807787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30778285087828700513077049 23083713815871525384807787)
    ·
      refine ⟨34625570723807288077211681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23083713815871525384807787 34625570723807288077211681)
      ·
        refine ⟨25969178042855466057908761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34625570723807288077211681 25969178042855466057908761)
        ·
          refine ⟨19476883532141599543431571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25969178042855466057908761 19476883532141599543431571)
          ·
            refine ⟨29215325298212399315147357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19476883532141599543431571 29215325298212399315147357)
            ·
              refine ⟨10955746986829649743180259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29215325298212399315147357 10955746986829649743180259)
              ·
                refine ⟨16433620480244474614770389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10955746986829649743180259 16433620480244474614770389)
                ·
                  refine ⟨385162980005729873783681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16433620480244474614770389 385162980005729873783681)
                  ·
                    rfl

theorem cell20_843865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_843865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843865 prefixEnd_843865 := by exact prefixLift 843865
  have htrace : WordTrace (prefixWord ++ tailWord_843865) baseStart_843865 baseEnd_843865 := by
    simpa [prefixWord, tailWord_843865, baseEnd_843865] using wordTrace_append hprefix tailTrace_843865
  have hstable : (prefixWord ++ tailWord_843865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843865).length < 2 ^ (prefixWord ++ tailWord_843865).sum := by decide
  have hdescent : baseEnd_843865 < baseStart_843865 := by decide
  rcases family_descends (prefixWord ++ tailWord_843865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843926 : List Nat := [5, 3, 2, 1, 1, 8]
def baseStart_843926 : Nat := 118140960795 + 843926 * 2 ^ 59
def prefixEnd_843926 : Nat := 4983230072969 + 3 ^ 40 * 843926 * 2
def baseEnd_843926 : Nat := 14266326743254991583337

theorem tailTrace_843926 : CollatzResearch.WordTrace tailWord_843926 prefixEnd_843926 14266326743254991583337 := by
  unfold tailWord_843926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923781871287981745690477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20520339960405138620698421 1923781871287981745690477)
  ·
    refine ⟨721418201732993154633929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1923781871287981745690477 721418201732993154633929)
    ·
      refine ⟨541063651299744865975447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 721418201732993154633929 541063651299744865975447)
      ·
        refine ⟨811595476949617298963171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541063651299744865975447 811595476949617298963171)
        ·
          refine ⟨1217393215424425948444757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811595476949617298963171 1217393215424425948444757)
          ·
            refine ⟨14266326743254991583337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1217393215424425948444757 14266326743254991583337)
            ·
              rfl

theorem cell20_843926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 8].length) (baseStart_843926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843926 prefixEnd_843926 := by exact prefixLift 843926
  have htrace : WordTrace (prefixWord ++ tailWord_843926) baseStart_843926 baseEnd_843926 := by
    simpa [prefixWord, tailWord_843926, baseEnd_843926] using wordTrace_append hprefix tailTrace_843926
  have hstable : (prefixWord ++ tailWord_843926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843926).length < 2 ^ (prefixWord ++ tailWord_843926).sum := by decide
  have hdescent : baseEnd_843926 < baseStart_843926 := by decide
  rcases family_descends (prefixWord ++ tailWord_843926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843937 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 3]
def baseStart_843937 : Nat := 118140960795 + 843937 * 2 ^ 59
def prefixEnd_843937 : Nat := 4983230072969 + 3 ^ 40 * 843937 * 2
def baseEnd_843937 : Nat := 385195842767617623383387

theorem tailTrace_843937 : CollatzResearch.WordTrace tailWord_843937 prefixEnd_843937 385195842767617623383387 := by
  unfold tailWord_843937
  simp only [CollatzResearch.WordTrace]
  refine ⟨30780911143567856809698065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20520607429045237873132043 30780911143567856809698065)
  ·
    refine ⟨23085683357675892607273549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30780911143567856809698065 23085683357675892607273549)
    ·
      refine ⟨8657131259128459727727581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23085683357675892607273549 8657131259128459727727581)
      ·
        refine ⟨3246424222173172397897843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8657131259128459727727581 3246424222173172397897843)
        ·
          refine ⟨4869636333259758596846765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246424222173172397897843 4869636333259758596846765)
          ·
            refine ⟨1826113624972409473817537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4869636333259758596846765 1826113624972409473817537)
            ·
              refine ⟨1369585218729307105363153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826113624972409473817537 1369585218729307105363153)
              ·
                refine ⟨1027188914046980329022365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369585218729307105363153 1027188914046980329022365)
                ·
                  refine ⟨385195842767617623383387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027188914046980329022365 385195842767617623383387)
                  ·
                    rfl

theorem cell20_843937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_843937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843937 prefixEnd_843937 := by exact prefixLift 843937
  have htrace : WordTrace (prefixWord ++ tailWord_843937) baseStart_843937 baseEnd_843937 := by
    simpa [prefixWord, tailWord_843937, baseEnd_843937] using wordTrace_append hprefix tailTrace_843937
  have hstable : (prefixWord ++ tailWord_843937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843937).length < 2 ^ (prefixWord ++ tailWord_843937).sum := by decide
  have hdescent : baseEnd_843937 < baseStart_843937 := by decide
  rcases family_descends (prefixWord ++ tailWord_843937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843979 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_843979 : Nat := 118140960795 + 843979 * 2 ^ 59
def prefixEnd_843979 : Nat := 4983230072969 + 3 ^ 40 * 843979 * 2
def baseEnd_843979 : Nat := 385215012712052143983215

theorem tailTrace_843979 : CollatzResearch.WordTrace tailWord_843979 prefixEnd_843979 385215012712052143983215 := by
  unfold tailWord_843979
  simp only [CollatzResearch.WordTrace]
  refine ⟨30782443009415697982726991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20521628672943798655151327 30782443009415697982726991)
  ·
    refine ⟨46173664514123546974090487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30782443009415697982726991 46173664514123546974090487)
    ·
      refine ⟨69260496771185320461135731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46173664514123546974090487 69260496771185320461135731)
      ·
        refine ⟨103890745156777980691703597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69260496771185320461135731 103890745156777980691703597)
        ·
          refine ⟨38959029433791742759388849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103890745156777980691703597 38959029433791742759388849)
          ·
            refine ⟨29219272075343807069541637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38959029433791742759388849 29219272075343807069541637)
            ·
              refine ⟨5478613514126963825539057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29219272075343807069541637 5478613514126963825539057)
              ·
                refine ⟨4108960135595222869154293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5478613514126963825539057 4108960135595222869154293)
                ·
                  refine ⟨385215012712052143983215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4108960135595222869154293 385215012712052143983215)
                  ·
                    rfl

theorem cell20_843979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_843979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843979 prefixEnd_843979 := by exact prefixLift 843979
  have htrace : WordTrace (prefixWord ++ tailWord_843979) baseStart_843979 baseEnd_843979 := by
    simpa [prefixWord, tailWord_843979, baseEnd_843979] using wordTrace_append hprefix tailTrace_843979
  have hstable : (prefixWord ++ tailWord_843979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843979).length < 2 ^ (prefixWord ++ tailWord_843979).sum := by decide
  have hdescent : baseEnd_843979 < baseStart_843979 := by decide
  rcases family_descends (prefixWord ++ tailWord_843979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_843989 : List Nat := [1, 3, 2, 4, 2, 1, 7]
def baseStart_843989 : Nat := 118140960795 + 843989 * 2 ^ 59
def prefixEnd_843989 : Nat := 4983230072969 + 3 ^ 40 * 843989 * 2
def baseEnd_843989 : Nat := 42802175220504061516649

theorem tailTrace_843989 : CollatzResearch.WordTrace tailWord_843989 prefixEnd_843989 42802175220504061516649 := by
  unfold tailWord_843989
  simp only [CollatzResearch.WordTrace]
  refine ⟨30782807739379469690591021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20521871826252979793727347 30782807739379469690591021)
  ·
    refine ⟨11543552902267301133971633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30782807739379469690591021 11543552902267301133971633)
    ·
      refine ⟨8657664676700475850478725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11543552902267301133971633 8657664676700475850478725)
      ·
        refine ⟨1623312126881339221964761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8657664676700475850478725 1623312126881339221964761)
        ·
          refine ⟨1217484095161004416473571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1623312126881339221964761 1217484095161004416473571)
          ·
            refine ⟨1826226142741506624710357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217484095161004416473571 1826226142741506624710357)
            ·
              refine ⟨42802175220504061516649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1826226142741506624710357 42802175220504061516649)
              ·
                rfl

theorem cell20_843989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 7].length) (baseStart_843989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_843989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_843989 prefixEnd_843989 := by exact prefixLift 843989
  have htrace : WordTrace (prefixWord ++ tailWord_843989) baseStart_843989 baseEnd_843989 := by
    simpa [prefixWord, tailWord_843989, baseEnd_843989] using wordTrace_append hprefix tailTrace_843989
  have hstable : (prefixWord ++ tailWord_843989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_843989).length < 2 ^ (prefixWord ++ tailWord_843989).sum := by decide
  have hdescent : baseEnd_843989 < baseStart_843989 := by decide
  rcases family_descends (prefixWord ++ tailWord_843989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844010 : List Nat := [3, 1, 3, 1, 1, 2, 2, 7]
def baseStart_844010 : Nat := 118140960795 + 844010 * 2 ^ 59
def prefixEnd_844010 : Nat := 4983230072969 + 3 ^ 40 * 844010 * 2
def baseEnd_844010 : Nat := 128409720652251271316585

theorem tailTrace_844010 : CollatzResearch.WordTrace tailWord_844010 prefixEnd_844010 128409720652251271316585 := by
  unfold tailWord_844010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7695893418075847569276371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20522382448202260184736989 7695893418075847569276371)
  ·
    refine ⟨11543840127113771353914557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7695893418075847569276371 11543840127113771353914557)
    ·
      refine ⟨4328940047667664257717959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11543840127113771353914557 4328940047667664257717959)
      ·
        refine ⟨6493410071501496386576939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4328940047667664257717959 6493410071501496386576939)
        ·
          refine ⟨9740115107252244579865409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493410071501496386576939 9740115107252244579865409)
          ·
            refine ⟨7305086330439183434899057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9740115107252244579865409 7305086330439183434899057)
            ·
              refine ⟨5478814747829387576174293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7305086330439183434899057 5478814747829387576174293)
              ·
                refine ⟨128409720652251271316585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5478814747829387576174293 128409720652251271316585)
                ·
                  rfl

theorem cell20_844010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_844010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844010 prefixEnd_844010 := by exact prefixLift 844010
  have htrace : WordTrace (prefixWord ++ tailWord_844010) baseStart_844010 baseEnd_844010 := by
    simpa [prefixWord, tailWord_844010, baseEnd_844010] using wordTrace_append hprefix tailTrace_844010
  have hstable : (prefixWord ++ tailWord_844010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844010).length < 2 ^ (prefixWord ++ tailWord_844010).sum := by decide
  have hdescent : baseEnd_844010 < baseStart_844010 := by decide
  rcases family_descends (prefixWord ++ tailWord_844010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844068 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 3]
def baseStart_844068 : Nat := 118140960795 + 844068 * 2 ^ 59
def prefixEnd_844068 : Nat := 4983230072969 + 3 ^ 40 * 844068 * 2
def baseEnd_844068 : Nat := 385255634737163390016185

theorem tailTrace_844068 : CollatzResearch.WordTrace tailWord_844068 prefixEnd_844068 385255634737163390016185 := by
  unfold tailWord_844068
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392844553046633091358429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20523792737395510788477905 15392844553046633091358429)
  ·
    refine ⟨5772316707392487409259411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15392844553046633091358429 5772316707392487409259411)
    ·
      refine ⟨8658475061088731113889117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5772316707392487409259411 8658475061088731113889117)
      ·
        refine ⟨3246928147908274167708419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8658475061088731113889117 3246928147908274167708419)
        ·
          refine ⟨4870392221862411251562629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246928147908274167708419 4870392221862411251562629)
          ·
            refine ⟨913198541599202109667993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4870392221862411251562629 913198541599202109667993)
            ·
              refine ⟨684898906199401582250995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913198541599202109667993 684898906199401582250995)
              ·
                refine ⟨1027348359299102373376493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684898906199401582250995 1027348359299102373376493)
                ·
                  refine ⟨385255634737163390016185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027348359299102373376493 385255634737163390016185)
                  ·
                    rfl

theorem cell20_844068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_844068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844068 prefixEnd_844068 := by exact prefixLift 844068
  have htrace : WordTrace (prefixWord ++ tailWord_844068) baseStart_844068 baseEnd_844068 := by
    simpa [prefixWord, tailWord_844068, baseEnd_844068] using wordTrace_append hprefix tailTrace_844068
  have hstable : (prefixWord ++ tailWord_844068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844068).length < 2 ^ (prefixWord ++ tailWord_844068).sum := by decide
  have hdescent : baseEnd_844068 < baseStart_844068 := by decide
  rcases family_descends (prefixWord ++ tailWord_844068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844113 : List Nat := [1, 2, 2, 1, 4, 2, 4, 2, 2]
def baseStart_844113 : Nat := 118140960795 + 844113 * 2 ^ 59
def prefixEnd_844113 : Nat := 4983230072969 + 3 ^ 40 * 844113 * 2
def baseEnd_844113 : Nat := 385276173963343233516001

theorem tailTrace_844113 : CollatzResearch.WordTrace tailWord_844113 prefixEnd_844113 385276173963343233516001 := by
  unfold tailWord_844113
  simp only [CollatzResearch.WordTrace]
  refine ⟨30787330390930238868104993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20524886927286825912069995 30787330390930238868104993)
  ·
    refine ⟨23090497793197679151078745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30787330390930238868104993 23090497793197679151078745)
    ·
      refine ⟨17317873344898259363309059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23090497793197679151078745 17317873344898259363309059)
      ·
        refine ⟨25976810017347389044963589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17317873344898259363309059 25976810017347389044963589)
        ·
          refine ⟨4870651878252635445930673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25976810017347389044963589 4870651878252635445930673)
          ·
            refine ⟨3652988908689476584448005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4870651878252635445930673 3652988908689476584448005)
            ·
              refine ⟨684935420379276859584001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3652988908689476584448005 684935420379276859584001)
              ·
                refine ⟨513701565284457644688001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684935420379276859584001 513701565284457644688001)
                ·
                  refine ⟨385276173963343233516001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513701565284457644688001 385276173963343233516001)
                  ·
                    rfl

theorem cell20_844113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_844113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844113 prefixEnd_844113 := by exact prefixLift 844113
  have htrace : WordTrace (prefixWord ++ tailWord_844113) baseStart_844113 baseEnd_844113 := by
    simpa [prefixWord, tailWord_844113, baseEnd_844113] using wordTrace_append hprefix tailTrace_844113
  have hstable : (prefixWord ++ tailWord_844113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844113).length < 2 ^ (prefixWord ++ tailWord_844113).sum := by decide
  have hdescent : baseEnd_844113 < baseStart_844113 := by decide
  rcases family_descends (prefixWord ++ tailWord_844113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844141 : List Nat := [1, 5, 1, 1, 1, 2, 5, 4]
def baseStart_844141 : Nat := 118140960795 + 844141 * 2 ^ 59
def prefixEnd_844141 : Nat := 4983230072969 + 3 ^ 40 * 844141 * 2
def baseEnd_844141 : Nat := 128429651308766526860851

theorem tailTrace_844141 : CollatzResearch.WordTrace tailWord_844141 prefixEnd_844141 128429651308766526860851 := by
  unfold tailWord_844141
  simp only [CollatzResearch.WordTrace]
  refine ⟨30788351634828799650124277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20525567756552533100082851 30788351634828799650124277)
  ·
    refine ⟨2886407965765199967199151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30788351634828799650124277 2886407965765199967199151)
    ·
      refine ⟨4329611948647799950798727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2886407965765199967199151 4329611948647799950798727)
      ·
        refine ⟨6494417922971699926198091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329611948647799950798727 6494417922971699926198091)
        ·
          refine ⟨9741626884457549889297137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6494417922971699926198091 9741626884457549889297137)
          ·
            refine ⟨7306220163343162416972853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9741626884457549889297137 7306220163343162416972853)
            ·
              refine ⟨684958140313421476591205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7306220163343162416972853 684958140313421476591205)
              ·
                refine ⟨128429651308766526860851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 684958140313421476591205 128429651308766526860851)
                ·
                  rfl

theorem cell20_844141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 4].length) (baseStart_844141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844141 prefixEnd_844141 := by exact prefixLift 844141
  have htrace : WordTrace (prefixWord ++ tailWord_844141) baseStart_844141 baseEnd_844141 := by
    simpa [prefixWord, tailWord_844141, baseEnd_844141] using wordTrace_append hprefix tailTrace_844141
  have hstable : (prefixWord ++ tailWord_844141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844141).length < 2 ^ (prefixWord ++ tailWord_844141).sum := by decide
  have hdescent : baseEnd_844141 < baseStart_844141 := by decide
  rcases family_descends (prefixWord ++ tailWord_844141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844172 : List Nat := [2, 2, 1, 2, 1, 4, 2, 4, 2]
def baseStart_844172 : Nat := 118140960795 + 844172 * 2 ^ 59
def prefixEnd_844172 : Nat := 4983230072969 + 3 ^ 40 * 844172 * 2
def baseEnd_844172 : Nat := 385303103171001250549093

theorem tailTrace_844172 : CollatzResearch.WordTrace tailWord_844172 prefixEnd_844172 385303103171001250549093 := by
  unfold tailWord_844172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15394741148858245972251385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20526321531810994629668513 15394741148858245972251385)
  ·
    refine ⟨11546055861643684479188539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15394741148858245972251385 11546055861643684479188539)
    ·
      refine ⟨17319083792465526718782809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11546055861643684479188539 17319083792465526718782809)
      ·
        refine ⟨12989312844349145039087107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17319083792465526718782809 12989312844349145039087107)
        ·
          refine ⟨19483969266523717558630661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12989312844349145039087107 19483969266523717558630661)
          ·
            refine ⟨3653244237473197042243249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19483969266523717558630661 3653244237473197042243249)
            ·
              refine ⟨2739933178104897781682437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3653244237473197042243249 2739933178104897781682437)
              ·
                refine ⟨513737470894668334065457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2739933178104897781682437 513737470894668334065457)
                ·
                  refine ⟨385303103171001250549093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513737470894668334065457 385303103171001250549093)
                  ·
                    rfl

theorem cell20_844172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_844172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844172 prefixEnd_844172 := by exact prefixLift 844172
  have htrace : WordTrace (prefixWord ++ tailWord_844172) baseStart_844172 baseEnd_844172 := by
    simpa [prefixWord, tailWord_844172, baseEnd_844172] using wordTrace_append hprefix tailTrace_844172
  have hstable : (prefixWord ++ tailWord_844172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844172).length < 2 ^ (prefixWord ++ tailWord_844172).sum := by decide
  have hdescent : baseEnd_844172 < baseStart_844172 := by decide
  rcases family_descends (prefixWord ++ tailWord_844172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844202 : List Nat := [3, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_844202 : Nat := 118140960795 + 844202 * 2 ^ 59
def prefixEnd_844202 : Nat := 4983230072969 + 3 ^ 40 * 844202 * 2
def baseEnd_844202 : Nat := 385316795988454479548971

theorem tailTrace_844202 : CollatzResearch.WordTrace tailWord_844202 prefixEnd_844202 385316795988454479548971 := by
  unfold tailWord_844202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697644121901951767023715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20527050991738538045396573 7697644121901951767023715)
  ·
    refine ⟨11546466182852927650535573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7697644121901951767023715 11546466182852927650535573)
    ·
      refine ⟨541240602321230983618855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11546466182852927650535573 541240602321230983618855)
      ·
        refine ⟨811860903481846475428283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541240602321230983618855 811860903481846475428283)
        ·
          refine ⟨1217791355222769713142425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811860903481846475428283 1217791355222769713142425)
          ·
            refine ⟨913343516417077284856819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1217791355222769713142425 913343516417077284856819)
            ·
              refine ⟨1370015274625615927285229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913343516417077284856819 1370015274625615927285229)
              ·
                refine ⟨513755727984605972731961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1370015274625615927285229 513755727984605972731961)
                ·
                  refine ⟨385316795988454479548971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513755727984605972731961 385316795988454479548971)
                  ·
                    rfl

theorem cell20_844202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_844202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844202 prefixEnd_844202 := by exact prefixLift 844202
  have htrace : WordTrace (prefixWord ++ tailWord_844202) baseStart_844202 baseEnd_844202 := by
    simpa [prefixWord, tailWord_844202, baseEnd_844202] using wordTrace_append hprefix tailTrace_844202
  have hstable : (prefixWord ++ tailWord_844202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844202).length < 2 ^ (prefixWord ++ tailWord_844202).sum := by decide
  have hdescent : baseEnd_844202 < baseStart_844202 := by decide
  rcases family_descends (prefixWord ++ tailWord_844202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844231 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_844231 : Nat := 118140960795 + 844231 * 2 ^ 59
def prefixEnd_844231 : Nat := 4983230072969 + 3 ^ 40 * 844231 * 2
def baseEnd_844231 : Nat := 385330032378659267582185

theorem tailTrace_844231 : CollatzResearch.WordTrace tailWord_844231 prefixEnd_844231 385330032378659267582185 := by
  unfold tailWord_844231
  simp only [CollatzResearch.WordTrace]
  refine ⟨30791634204502745020900547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20527756136335163347267031 30791634204502745020900547)
  ·
    refine ⟨46187451306754117531350821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30791634204502745020900547 46187451306754117531350821)
    ·
      refine ⟨8660147120016397037128279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46187451306754117531350821 8660147120016397037128279)
      ·
        refine ⟨12990220680024595555692419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8660147120016397037128279 12990220680024595555692419)
        ·
          refine ⟨19485331020036893333538629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12990220680024595555692419 19485331020036893333538629)
          ·
            refine ⟨3653499566256917500038493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19485331020036893333538629 3653499566256917500038493)
            ·
              refine ⟨1370062337346344062514435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3653499566256917500038493 1370062337346344062514435)
              ·
                refine ⟨2055093506019516093771653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370062337346344062514435 2055093506019516093771653)
                ·
                  refine ⟨385330032378659267582185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2055093506019516093771653 385330032378659267582185)
                  ·
                    rfl

theorem cell20_844231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_844231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844231 prefixEnd_844231 := by exact prefixLift 844231
  have htrace : WordTrace (prefixWord ++ tailWord_844231) baseStart_844231 baseEnd_844231 := by
    simpa [prefixWord, tailWord_844231, baseEnd_844231] using wordTrace_append hprefix tailTrace_844231
  have hstable : (prefixWord ++ tailWord_844231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844231).length < 2 ^ (prefixWord ++ tailWord_844231).sum := by decide
  have hdescent : baseEnd_844231 < baseStart_844231 := by decide
  rcases family_descends (prefixWord ++ tailWord_844231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844276 : List Nat := [2, 6, 12]
def baseStart_844276 : Nat := 118140960795 + 844276 * 2 ^ 59
def prefixEnd_844276 : Nat := 4983230072969 + 3 ^ 40 * 844276 * 2
def baseEnd_844276 : Nat := 528601607139696997369

theorem tailTrace_844276 : CollatzResearch.WordTrace tailWord_844276 prefixEnd_844276 528601607139696997369 := by
  unfold tailWord_844276
  simp only [CollatzResearch.WordTrace]
  refine ⟨15396637744669858853144341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20528850326226478470859121 15396637744669858853144341)
  ·
    refine ⟨721717394281399633741141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15396637744669858853144341 721717394281399633741141)
    ·
      refine ⟨528601607139696997369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 721717394281399633741141 528601607139696997369)
      ·
        rfl

theorem cell20_844276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 12].length) (baseStart_844276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844276 prefixEnd_844276 := by exact prefixLift 844276
  have htrace : WordTrace (prefixWord ++ tailWord_844276) baseStart_844276 baseEnd_844276 := by
    simpa [prefixWord, tailWord_844276, baseEnd_844276] using wordTrace_append hprefix tailTrace_844276
  have hstable : (prefixWord ++ tailWord_844276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844276).length < 2 ^ (prefixWord ++ tailWord_844276).sum := by decide
  have hdescent : baseEnd_844276 < baseStart_844276 := by decide
  rcases family_descends (prefixWord ++ tailWord_844276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844297 : List Nat := [1, 2, 1, 1, 3, 1, 2, 9]
def baseStart_844297 : Nat := 118140960795 + 844297 * 2 ^ 59
def prefixEnd_844297 : Nat := 4983230072969 + 3 ^ 40 * 844297 * 2
def baseEnd_844297 : Nat := 128453385525685457127305

theorem tailTrace_844297 : CollatzResearch.WordTrace tailWord_844297 prefixEnd_844297 128453385525685457127305 := by
  unfold tailWord_844297
  simp only [CollatzResearch.WordTrace]
  refine ⟨30794041422263638292803145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20529360948175758861868763 30794041422263638292803145)
  ·
    refine ⟨23095531066697728719602359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30794041422263638292803145 23095531066697728719602359)
    ·
      refine ⟨34643296600046593079403539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23095531066697728719602359 34643296600046593079403539)
      ·
        refine ⟨51964944900069889619105309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34643296600046593079403539 51964944900069889619105309)
        ·
          refine ⟨19486854337526208607164491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51964944900069889619105309 19486854337526208607164491)
          ·
            refine ⟨29230281506289312910746737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19486854337526208607164491 29230281506289312910746737)
            ·
              refine ⟨21922711129716984683060053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29230281506289312910746737 21922711129716984683060053)
              ·
                refine ⟨128453385525685457127305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21922711129716984683060053 128453385525685457127305)
                ·
                  rfl

theorem cell20_844297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_844297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844297 prefixEnd_844297 := by exact prefixLift 844297
  have htrace : WordTrace (prefixWord ++ tailWord_844297) baseStart_844297 baseEnd_844297 := by
    simpa [prefixWord, tailWord_844297, baseEnd_844297] using wordTrace_append hprefix tailTrace_844297
  have hstable : (prefixWord ++ tailWord_844297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844297).length < 2 ^ (prefixWord ++ tailWord_844297).sum := by decide
  have hdescent : baseEnd_844297 < baseStart_844297 := by decide
  rcases family_descends (prefixWord ++ tailWord_844297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844300 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_844300 : Nat := 118140960795 + 844300 * 2 ^ 59
def prefixEnd_844300 : Nat := 4983230072969 + 3 ^ 40 * 844300 * 2
def baseEnd_844300 : Nat := 385361525858801694281903

theorem tailTrace_844300 : CollatzResearch.WordTrace tailWord_844300 prefixEnd_844300 385361525858801694281903 := by
  unfold tailWord_844300
  simp only [CollatzResearch.WordTrace]
  refine ⟨15397075420626384902581177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20529433894168513203441569 15397075420626384902581177)
  ·
    refine ⟨11547806565469788676935883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15397075420626384902581177 11547806565469788676935883)
    ·
      refine ⟨17321709848204683015403825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11547806565469788676935883 17321709848204683015403825)
      ·
        refine ⟨12991282386153512261552869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17321709848204683015403825 12991282386153512261552869)
        ·
          refine ⟨2435865447403783549041163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12991282386153512261552869 2435865447403783549041163)
          ·
            refine ⟨3653798171105675323561745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435865447403783549041163 3653798171105675323561745)
            ·
              refine ⟨2740348628329256492671309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3653798171105675323561745 2740348628329256492671309)
              ·
                refine ⟨1027630735623471184751741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2740348628329256492671309 1027630735623471184751741)
                ·
                  refine ⟨385361525858801694281903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027630735623471184751741 385361525858801694281903)
                  ·
                    rfl

theorem cell20_844300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_844300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844300 prefixEnd_844300 := by exact prefixLift 844300
  have htrace : WordTrace (prefixWord ++ tailWord_844300) baseStart_844300 baseEnd_844300 := by
    simpa [prefixWord, tailWord_844300, baseEnd_844300] using wordTrace_append hprefix tailTrace_844300
  have hstable : (prefixWord ++ tailWord_844300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844300).length < 2 ^ (prefixWord ++ tailWord_844300).sum := by decide
  have hdescent : baseEnd_844300 < baseStart_844300 := by decide
  rcases family_descends (prefixWord ++ tailWord_844300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844321 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_844321 : Nat := 118140960795 + 844321 * 2 ^ 59
def prefixEnd_844321 : Nat := 4983230072969 + 3 ^ 40 * 844321 * 2
def baseEnd_844321 : Nat := 385371110831018954581817

theorem tailTrace_844321 : CollatzResearch.WordTrace tailWord_844321 prefixEnd_844321 385371110831018954581817 := by
  unfold tailWord_844321
  simp only [CollatzResearch.WordTrace]
  refine ⟨30794916774176690391676817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20529944516117793594451211 30794916774176690391676817)
  ·
    refine ⟨23096187580632517793757613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30794916774176690391676817 23096187580632517793757613)
    ·
      refine ⟨8661070342737194172659105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23096187580632517793757613 8661070342737194172659105)
      ·
        refine ⟨6495802757052895629494329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8661070342737194172659105 6495802757052895629494329)
        ·
          refine ⟨4871852067789671722120747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6495802757052895629494329 4871852067789671722120747)
          ·
            refine ⟨7307778101684507583181121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4871852067789671722120747 7307778101684507583181121)
            ·
              refine ⟨5480833576263380687385841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7307778101684507583181121 5480833576263380687385841)
              ·
                refine ⟨4110625182197535515539381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5480833576263380687385841 4110625182197535515539381)
                ·
                  refine ⟨385371110831018954581817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4110625182197535515539381 385371110831018954581817)
                  ·
                    rfl

theorem cell20_844321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_844321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844321 prefixEnd_844321 := by exact prefixLift 844321
  have htrace : WordTrace (prefixWord ++ tailWord_844321) baseStart_844321 baseEnd_844321 := by
    simpa [prefixWord, tailWord_844321, baseEnd_844321] using wordTrace_append hprefix tailTrace_844321
  have hstable : (prefixWord ++ tailWord_844321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844321).length < 2 ^ (prefixWord ++ tailWord_844321).sum := by decide
  have hdescent : baseEnd_844321 < baseStart_844321 := by decide
  rcases family_descends (prefixWord ++ tailWord_844321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844334 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_844334 : Nat := 118140960795 + 844334 * 2 ^ 59
def prefixEnd_844334 : Nat := 4983230072969 + 3 ^ 40 * 844334 * 2
def baseEnd_844334 : Nat := 385377044385248687148431

theorem tailTrace_844334 : CollatzResearch.WordTrace tailWord_844334 prefixEnd_844334 385377044385248687148431 := by
  unfold tailWord_844334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849423865391199201487507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20530260615419729074600037 3849423865391199201487507)
  ·
    refine ⟨5774135798086798802231261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3849423865391199201487507 5774135798086798802231261)
    ·
      refine ⟨2165300924282549550836723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5774135798086798802231261 2165300924282549550836723)
      ·
        refine ⟨3247951386423824326255085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165300924282549550836723 3247951386423824326255085)
        ·
          refine ⟨1217981769908934122345657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3247951386423824326255085 1217981769908934122345657)
          ·
            refine ⟨913486327431700591759243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1217981769908934122345657 913486327431700591759243)
            ·
              refine ⟨1370229491147550887638865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913486327431700591759243 1370229491147550887638865)
              ·
                refine ⟨1027672118360663165729149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370229491147550887638865 1027672118360663165729149)
                ·
                  refine ⟨385377044385248687148431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027672118360663165729149 385377044385248687148431)
                  ·
                    rfl

theorem cell20_844334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_844334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844334 prefixEnd_844334 := by exact prefixLift 844334
  have htrace : WordTrace (prefixWord ++ tailWord_844334) baseStart_844334 baseEnd_844334 := by
    simpa [prefixWord, tailWord_844334, baseEnd_844334] using wordTrace_append hprefix tailTrace_844334
  have hstable : (prefixWord ++ tailWord_844334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844334).length < 2 ^ (prefixWord ++ tailWord_844334).sum := by decide
  have hdescent : baseEnd_844334 < baseStart_844334 := by decide
  rcases family_descends (prefixWord ++ tailWord_844334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844338 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_844338 : Nat := 118140960795 + 844338 * 2 ^ 59
def prefixEnd_844338 : Nat := 4983230072969 + 3 ^ 40 * 844338 * 2
def baseEnd_844338 : Nat := 385378870094242451015081

theorem tailTrace_844338 : CollatzResearch.WordTrace tailWord_844338 prefixEnd_844338 385378870094242451015081 := by
  unfold tailWord_844338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7698884203778775573761417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20530357876743401530030445 7698884203778775573761417)
  ·
    refine ⟨5774163152834081680321063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7698884203778775573761417 5774163152834081680321063)
    ·
      refine ⟨8661244729251122520481595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5774163152834081680321063 8661244729251122520481595)
      ·
        refine ⟨12991867093876683780722393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8661244729251122520481595 12991867093876683780722393)
        ·
          refine ⟨9743900320407512835541795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12991867093876683780722393 9743900320407512835541795)
          ·
            refine ⟨14615850480611269253312693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9743900320407512835541795 14615850480611269253312693)
            ·
              refine ⟨1370235982557306492498065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14615850480611269253312693 1370235982557306492498065)
              ·
                refine ⟨1027676986917979869373549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370235982557306492498065 1027676986917979869373549)
                ·
                  refine ⟨385378870094242451015081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027676986917979869373549 385378870094242451015081)
                  ·
                    rfl

theorem cell20_844338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_844338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844338 prefixEnd_844338 := by exact prefixLift 844338
  have htrace : WordTrace (prefixWord ++ tailWord_844338) baseStart_844338 baseEnd_844338 := by
    simpa [prefixWord, tailWord_844338, baseEnd_844338] using wordTrace_append hprefix tailTrace_844338
  have hstable : (prefixWord ++ tailWord_844338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844338).length < 2 ^ (prefixWord ++ tailWord_844338).sum := by decide
  have hdescent : baseEnd_844338 < baseStart_844338 := by decide
  rcases family_descends (prefixWord ++ tailWord_844338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844345 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_844345 : Nat := 118140960795 + 844345 * 2 ^ 59
def prefixEnd_844345 : Nat := 4983230072969 + 3 ^ 40 * 844345 * 2
def baseEnd_844345 : Nat := 385382065084981537781719

theorem tailTrace_844345 : CollatzResearch.WordTrace tailWord_844345 prefixEnd_844345 385382065084981537781719 := by
  unfold tailWord_844345
  simp only [CollatzResearch.WordTrace]
  refine ⟨30795792126089742490550489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20530528084059828327033659 30795792126089742490550489)
  ·
    refine ⟨23096844094567306867912867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30795792126089742490550489 23096844094567306867912867)
    ·
      refine ⟨34645266141850960301869301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23096844094567306867912867 34645266141850960301869301)
      ·
        refine ⟨3247993700798527528300247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34645266141850960301869301 3247993700798527528300247)
        ·
          refine ⟨4871990551197791292450371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3247993700798527528300247 4871990551197791292450371)
          ·
            refine ⟨7307985826796686938675557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4871990551197791292450371 7307985826796686938675557)
            ·
              refine ⟨1370247342524378801001667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7307985826796686938675557 1370247342524378801001667)
              ·
                refine ⟨2055371013786568201502501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370247342524378801001667 2055371013786568201502501)
                ·
                  refine ⟨385382065084981537781719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2055371013786568201502501 385382065084981537781719)
                  ·
                    rfl

theorem cell20_844345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_844345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844345 prefixEnd_844345 := by exact prefixLift 844345
  have htrace : WordTrace (prefixWord ++ tailWord_844345) baseStart_844345 baseEnd_844345 := by
    simpa [prefixWord, tailWord_844345, baseEnd_844345] using wordTrace_append hprefix tailTrace_844345
  have hstable : (prefixWord ++ tailWord_844345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844345).length < 2 ^ (prefixWord ++ tailWord_844345).sum := by decide
  have hdescent : baseEnd_844345 < baseStart_844345 := by decide
  rcases family_descends (prefixWord ++ tailWord_844345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844369 : List Nat := [1, 2, 2, 1, 3, 5, 2, 4]
def baseStart_844369 : Nat := 118140960795 + 844369 * 2 ^ 59
def prefixEnd_844369 : Nat := 4983230072969 + 3 ^ 40 * 844369 * 2
def baseEnd_844369 : Nat := 128464339779648040327207

theorem tailTrace_844369 : CollatzResearch.WordTrace tailWord_844369 prefixEnd_844369 128464339779648040327207 := by
  unfold tailWord_844369
  simp only [CollatzResearch.WordTrace]
  refine ⟨30796667478002794589424161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20531111652001863059616107 30796667478002794589424161)
  ·
    refine ⟨23097500608502095942068121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30796667478002794589424161 23097500608502095942068121)
    ·
      refine ⟨17323125456376571956551091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23097500608502095942068121 17323125456376571956551091)
      ·
        refine ⟨25984688184564857934826637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17323125456376571956551091 25984688184564857934826637)
        ·
          refine ⟨9744258069211821725559989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25984688184564857934826637 9744258069211821725559989)
          ·
            refine ⟨913524193988608286771249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9744258069211821725559989 913524193988608286771249)
            ·
              refine ⟨685143145491456215078437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913524193988608286771249 685143145491456215078437)
              ·
                refine ⟨128464339779648040327207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685143145491456215078437 128464339779648040327207)
                ·
                  rfl

theorem cell20_844369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 4].length) (baseStart_844369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844369 prefixEnd_844369 := by exact prefixLift 844369
  have htrace : WordTrace (prefixWord ++ tailWord_844369) baseStart_844369 baseEnd_844369 := by
    simpa [prefixWord, tailWord_844369, baseEnd_844369] using wordTrace_append hprefix tailTrace_844369
  have hstable : (prefixWord ++ tailWord_844369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844369).length < 2 ^ (prefixWord ++ tailWord_844369).sum := by decide
  have hdescent : baseEnd_844369 < baseStart_844369 := by decide
  rcases family_descends (prefixWord ++ tailWord_844369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844382 : List Nat := [4, 4, 1, 2, 2, 1, 6]
def baseStart_844382 : Nat := 118140960795 + 844382 * 2 ^ 59
def prefixEnd_844382 : Nat := 4983230072969 + 3 ^ 40 * 844382 * 2
def baseEnd_844382 : Nat := 42822105877019317060915

theorem tailTrace_844382 : CollatzResearch.WordTrace tailWord_844382 prefixEnd_844382 42822105877019317060915 := by
  unfold tailWord_844382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849642703369462226205925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20531427751303798539764933 3849642703369462226205925)
  ·
    refine ⟨721808006881774167413611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3849642703369462226205925 721808006881774167413611)
    ·
      refine ⟨1082712010322661251120417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 721808006881774167413611 1082712010322661251120417)
      ·
        refine ⟨812034007741995938340313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1082712010322661251120417 812034007741995938340313)
        ·
          refine ⟨609025505806496953755235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812034007741995938340313 609025505806496953755235)
          ·
            refine ⟨913538258709745430632853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609025505806496953755235 913538258709745430632853)
            ·
              refine ⟨42822105877019317060915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 913538258709745430632853 42822105877019317060915)
              ·
                rfl

theorem cell20_844382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 6].length) (baseStart_844382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844382 prefixEnd_844382 := by exact prefixLift 844382
  have htrace : WordTrace (prefixWord ++ tailWord_844382) baseStart_844382 baseEnd_844382 := by
    simpa [prefixWord, tailWord_844382, baseEnd_844382] using wordTrace_append hprefix tailTrace_844382
  have hstable : (prefixWord ++ tailWord_844382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844382).length < 2 ^ (prefixWord ++ tailWord_844382).sum := by decide
  have hdescent : baseEnd_844382 < baseStart_844382 := by decide
  rcases family_descends (prefixWord ++ tailWord_844382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844386 : List Nat := [3, 3, 2, 3, 1, 2, 6]
def baseStart_844386 : Nat := 118140960795 + 844386 * 2 ^ 59
def prefixEnd_844386 : Nat := 4983230072969 + 3 ^ 40 * 844386 * 2
def baseEnd_844386 : Nat := 42822308733574179712765

theorem tailTrace_844386 : CollatzResearch.WordTrace tailWord_844386 prefixEnd_844386 42822308733574179712765 := by
  unfold tailWord_844386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7699321879735301623198253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20531525012627470995195341 7699321879735301623198253)
  ·
    refine ⟨2887245704900738108699345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7699321879735301623198253 2887245704900738108699345)
    ·
      refine ⟨2165434278675553581524509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2887245704900738108699345 2165434278675553581524509)
      ·
        refine ⟨812037854503332593071691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2165434278675553581524509 812037854503332593071691)
        ·
          refine ⟨1218056781754998889607537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812037854503332593071691 1218056781754998889607537)
          ·
            refine ⟨913542586316249167205653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218056781754998889607537 913542586316249167205653)
            ·
              refine ⟨42822308733574179712765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 913542586316249167205653 42822308733574179712765)
              ·
                rfl

theorem cell20_844386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 6].length) (baseStart_844386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844386 prefixEnd_844386 := by exact prefixLift 844386
  have htrace : WordTrace (prefixWord ++ tailWord_844386) baseStart_844386 baseEnd_844386 := by
    simpa [prefixWord, tailWord_844386, baseEnd_844386] using wordTrace_append hprefix tailTrace_844386
  have hstable : (prefixWord ++ tailWord_844386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844386).length < 2 ^ (prefixWord ++ tailWord_844386).sum := by decide
  have hdescent : baseEnd_844386 < baseStart_844386 := by decide
  rcases family_descends (prefixWord ++ tailWord_844386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844400 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 4]
def baseStart_844400 : Nat := 118140960795 + 844400 * 2 ^ 59
def prefixEnd_844400 : Nat := 4983230072969 + 3 ^ 40 * 844400 * 2
def baseEnd_844400 : Nat := 385407168583645790948161

theorem tailTrace_844400 : CollatzResearch.WordTrace tailWord_844400 prefixEnd_844400 385407168583645790948161 := by
  unfold tailWord_844400
  simp only [CollatzResearch.WordTrace]
  refine ⟨15398899070445243441901327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20531865427260324589201769 15398899070445243441901327)
  ·
    refine ⟨23098348605667865162851991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15398899070445243441901327 23098348605667865162851991)
    ·
      refine ⟨34647522908501797744277987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23098348605667865162851991 34647522908501797744277987)
      ·
        refine ⟨51971284362752696616416981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34647522908501797744277987 51971284362752696616416981)
        ·
          refine ⟨1218076977252016326947273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 51971284362752696616416981 1218076977252016326947273)
          ·
            refine ⟨913557732939012245210455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218076977252016326947273 913557732939012245210455)
            ·
              refine ⟨1370336599408518367815683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913557732939012245210455 1370336599408518367815683)
              ·
                refine ⟨2055504899112777551723525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370336599408518367815683 2055504899112777551723525)
                ·
                  refine ⟨385407168583645790948161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2055504899112777551723525 385407168583645790948161)
                  ·
                    rfl

theorem cell20_844400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_844400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844400 prefixEnd_844400 := by exact prefixLift 844400
  have htrace : WordTrace (prefixWord ++ tailWord_844400) baseStart_844400 baseEnd_844400 := by
    simpa [prefixWord, tailWord_844400, baseEnd_844400] using wordTrace_append hprefix tailTrace_844400
  have hstable : (prefixWord ++ tailWord_844400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844400).length < 2 ^ (prefixWord ++ tailWord_844400).sum := by decide
  have hdescent : baseEnd_844400 < baseStart_844400 := by decide
  rcases family_descends (prefixWord ++ tailWord_844400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844449 : List Nat := [1, 2, 3, 3, 11]
def baseStart_844449 : Nat := 118140960795 + 844449 * 2 ^ 59
def prefixEnd_844449 : Nat := 4983230072969 + 3 ^ 40 * 844449 * 2
def baseEnd_844449 : Nat := 4758389302701474053267

theorem tailTrace_844449 : CollatzResearch.WordTrace tailWord_844449 prefixEnd_844449 4758389302701474053267 := by
  unfold tailWord_844449
  simp only [CollatzResearch.WordTrace]
  refine ⟨30799585317712968252336401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20533056878475312168224267 30799585317712968252336401)
  ·
    refine ⟨23099688988284726189252301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30799585317712968252336401 23099688988284726189252301)
    ·
      refine ⟨8662383370606772320969613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23099688988284726189252301 8662383370606772320969613)
      ·
        refine ⟨3248393763977539620363605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8662383370606772320969613 3248393763977539620363605)
        ·
          refine ⟨4758389302701474053267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3248393763977539620363605 4758389302701474053267)
          ·
            rfl

theorem cell20_844449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 11].length) (baseStart_844449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844449 prefixEnd_844449 := by exact prefixLift 844449
  have htrace : WordTrace (prefixWord ++ tailWord_844449) baseStart_844449 baseEnd_844449 := by
    simpa [prefixWord, tailWord_844449, baseEnd_844449] using wordTrace_append hprefix tailTrace_844449
  have hstable : (prefixWord ++ tailWord_844449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844449).length < 2 ^ (prefixWord ++ tailWord_844449).sum := by decide
  have hdescent : baseEnd_844449 < baseStart_844449 := by decide
  rcases family_descends (prefixWord ++ tailWord_844449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844452 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 3]
def baseStart_844452 : Nat := 118140960795 + 844452 * 2 ^ 59
def prefixEnd_844452 : Nat := 4983230072969 + 3 ^ 40 * 844452 * 2
def baseEnd_844452 : Nat := 385430902800564721214615

theorem tailTrace_844452 : CollatzResearch.WordTrace tailWord_844452 prefixEnd_844452 385430902800564721214615 := by
  unfold tailWord_844452
  simp only [CollatzResearch.WordTrace]
  refine ⟨15399847368351049882347805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20533129824468066509797073 15399847368351049882347805)
  ·
    refine ⟨5774942763131643705880427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15399847368351049882347805 5774942763131643705880427)
    ·
      refine ⟨8662414144697465558820641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5774942763131643705880427 8662414144697465558820641)
      ·
        refine ⟨6496810608523099169115481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8662414144697465558820641 6496810608523099169115481)
        ·
          refine ⟨4872607956392324376836611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6496810608523099169115481 4872607956392324376836611)
          ·
            refine ⟨7308911934588486565254917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872607956392324376836611 7308911934588486565254917)
            ·
              refine ⟨1370420987735341230985297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7308911934588486565254917 1370420987735341230985297)
              ·
                refine ⟨1027815740801505923238973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370420987735341230985297 1027815740801505923238973)
                ·
                  refine ⟨385430902800564721214615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027815740801505923238973 385430902800564721214615)
                  ·
                    rfl

theorem cell20_844452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_844452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844452 prefixEnd_844452 := by exact prefixLift 844452
  have htrace : WordTrace (prefixWord ++ tailWord_844452) baseStart_844452 baseEnd_844452 := by
    simpa [prefixWord, tailWord_844452, baseEnd_844452] using wordTrace_append hprefix tailTrace_844452
  have hstable : (prefixWord ++ tailWord_844452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844452).length < 2 ^ (prefixWord ++ tailWord_844452).sum := by decide
  have hdescent : baseEnd_844452 < baseStart_844452 := by decide
  rcases family_descends (prefixWord ++ tailWord_844452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844462 : List Nat := [4, 1, 4, 1, 1, 3, 1, 5]
def baseStart_844462 : Nat := 118140960795 + 844462 * 2 ^ 59
def prefixEnd_844462 : Nat := 4983230072969 + 3 ^ 40 * 844462 * 2
def baseEnd_844462 : Nat := 128478489024349710293747

theorem tailTrace_844462 : CollatzResearch.WordTrace tailWord_844462 prefixEnd_844462 128478489024349710293747 := by
  unfold tailWord_844462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850007433333233934069955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20533372977777247648373093 3850007433333233934069955)
  ·
    refine ⟨5775011149999850901104933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3850007433333233934069955 5775011149999850901104933)
    ·
      refine ⟨1082814590624972043957175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5775011149999850901104933 1082814590624972043957175)
      ·
        refine ⟨1624221885937458065935763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082814590624972043957175 1624221885937458065935763)
        ·
          refine ⟨2436332828906187098903645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624221885937458065935763 2436332828906187098903645)
          ·
            refine ⟨913624810839820162088867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2436332828906187098903645 913624810839820162088867)
            ·
              refine ⟨1370437216259730243133301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913624810839820162088867 1370437216259730243133301)
              ·
                refine ⟨128478489024349710293747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1370437216259730243133301 128478489024349710293747)
                ·
                  rfl

theorem cell20_844462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_844462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844462 prefixEnd_844462 := by exact prefixLift 844462
  have htrace : WordTrace (prefixWord ++ tailWord_844462) baseStart_844462 baseEnd_844462 := by
    simpa [prefixWord, tailWord_844462, baseEnd_844462] using wordTrace_append hprefix tailTrace_844462
  have hstable : (prefixWord ++ tailWord_844462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844462).length < 2 ^ (prefixWord ++ tailWord_844462).sum := by decide
  have hdescent : baseEnd_844462 < baseStart_844462 := by decide
  rcases family_descends (prefixWord ++ tailWord_844462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844480 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_844480 : Nat := 118140960795 + 844480 * 2 ^ 59
def prefixEnd_844480 : Nat := 4983230072969 + 3 ^ 40 * 844480 * 2
def baseEnd_844480 : Nat := 385443682763521068281167

theorem tailTrace_844480 : CollatzResearch.WordTrace tailWord_844480 prefixEnd_844480 385443682763521068281167 := by
  unfold tailWord_844480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15400357990300330273357447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20533810653733773697809929 15400357990300330273357447)
  ·
    refine ⟨23100536985450495410036171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15400357990300330273357447 23100536985450495410036171)
    ·
      refine ⟨34650805478175743115054257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23100536985450495410036171 34650805478175743115054257)
      ·
        refine ⟨25988104108631807336290693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34650805478175743115054257 25988104108631807336290693)
        ·
          refine ⟨4872769520368463875554505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25988104108631807336290693 4872769520368463875554505)
          ·
            refine ⟨3654577140276347906665879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4872769520368463875554505 3654577140276347906665879)
            ·
              refine ⟨5481865710414521859998819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3654577140276347906665879 5481865710414521859998819)
              ·
                refine ⟨8222798565621782789998229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5481865710414521859998819 8222798565621782789998229)
                ·
                  refine ⟨385443682763521068281167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8222798565621782789998229 385443682763521068281167)
                  ·
                    rfl

theorem cell20_844480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_844480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844480 prefixEnd_844480 := by exact prefixLift 844480
  have htrace : WordTrace (prefixWord ++ tailWord_844480) baseStart_844480 baseEnd_844480 := by
    simpa [prefixWord, tailWord_844480, baseEnd_844480] using wordTrace_append hprefix tailTrace_844480
  have hstable : (prefixWord ++ tailWord_844480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844480).length < 2 ^ (prefixWord ++ tailWord_844480).sum := by decide
  have hdescent : baseEnd_844480 < baseStart_844480 := by decide
  rcases family_descends (prefixWord ++ tailWord_844480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844511 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_844511 : Nat := 118140960795 + 844511 * 2 ^ 59
def prefixEnd_844511 : Nat := 4983230072969 + 3 ^ 40 * 844511 * 2
def baseEnd_844511 : Nat := 385457832008222738247707

theorem tailTrace_844511 : CollatzResearch.WordTrace tailWord_844511 prefixEnd_844511 385457832008222738247707 := by
  unfold tailWord_844511
  simp only [CollatzResearch.WordTrace]
  refine ⟨30801846643488352841093387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20534564428992235227395591 30801846643488352841093387)
  ·
    refine ⟨46202769965232529261640081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30801846643488352841093387 46202769965232529261640081)
    ·
      refine ⟨34652077473924396946230061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46202769965232529261640081 34652077473924396946230061)
      ·
        refine ⟨12994529052721648854836273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34652077473924396946230061 12994529052721648854836273)
        ·
          refine ⟨9745896789541236641127205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12994529052721648854836273 9745896789541236641127205)
          ·
            refine ⟨1827355648038981870211351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9745896789541236641127205 1827355648038981870211351)
            ·
              refine ⟨2741033472058472805317027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827355648038981870211351 2741033472058472805317027)
              ·
                refine ⟨4111550208087709207975541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741033472058472805317027 4111550208087709207975541)
                ·
                  refine ⟨385457832008222738247707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4111550208087709207975541 385457832008222738247707)
                  ·
                    rfl

theorem cell20_844511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_844511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844511 prefixEnd_844511 := by exact prefixLift 844511
  have htrace : WordTrace (prefixWord ++ tailWord_844511) baseStart_844511 baseEnd_844511 := by
    simpa [prefixWord, tailWord_844511, baseEnd_844511] using wordTrace_append hprefix tailTrace_844511
  have hstable : (prefixWord ++ tailWord_844511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844511).length < 2 ^ (prefixWord ++ tailWord_844511).sum := by decide
  have hdescent : baseEnd_844511 < baseStart_844511 := by decide
  rcases family_descends (prefixWord ++ tailWord_844511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844528 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 3]
def baseStart_844528 : Nat := 118140960795 + 844528 * 2 ^ 59
def prefixEnd_844528 : Nat := 4983230072969 + 3 ^ 40 * 844528 * 2
def baseEnd_844528 : Nat := 385465591271446234680971

theorem tailTrace_844528 : CollatzResearch.WordTrace tailWord_844528 prefixEnd_844528 385465591271446234680971 := by
  unfold tailWord_844528
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401233342213382372231119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20534977789617843162974825 15401233342213382372231119)
  ·
    refine ⟨23101850013320073558346679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15401233342213382372231119 23101850013320073558346679)
    ·
      refine ⟨34652775019980110337520019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23101850013320073558346679 34652775019980110337520019)
      ·
        refine ⟨51979162529970165506280029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34652775019980110337520019 51979162529970165506280029)
        ·
          refine ⟨19492185948738812064855011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51979162529970165506280029 19492185948738812064855011)
          ·
            refine ⟨29238278923108218097282517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19492185948738812064855011 29238278923108218097282517)
            ·
              refine ⟨685272162260348861655059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29238278923108218097282517 685272162260348861655059)
              ·
                refine ⟨1027908243390523292482589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685272162260348861655059 1027908243390523292482589)
                ·
                  refine ⟨385465591271446234680971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1027908243390523292482589 385465591271446234680971)
                  ·
                    rfl

theorem cell20_844528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_844528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844528 prefixEnd_844528 := by exact prefixLift 844528
  have htrace : WordTrace (prefixWord ++ tailWord_844528) baseStart_844528 baseEnd_844528 := by
    simpa [prefixWord, tailWord_844528, baseEnd_844528] using wordTrace_append hprefix tailTrace_844528
  have hstable : (prefixWord ++ tailWord_844528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844528).length < 2 ^ (prefixWord ++ tailWord_844528).sum := by decide
  have hdescent : baseEnd_844528 < baseStart_844528 := by decide
  rcases family_descends (prefixWord ++ tailWord_844528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844552 : List Nat := [2, 1, 3, 2, 2, 2, 3, 3, 2]
def baseStart_844552 : Nat := 118140960795 + 844552 * 2 ^ 59
def prefixEnd_844552 : Nat := 4983230072969 + 3 ^ 40 * 844552 * 2
def baseEnd_844552 : Nat := 385476545525408817880873

theorem tailTrace_844552 : CollatzResearch.WordTrace tailWord_844552 prefixEnd_844552 385476545525408817880873 := by
  unfold tailWord_844552
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401671018169908421667955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20535561357559877895557273 15401671018169908421667955)
  ·
    refine ⟨23102506527254862632501933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15401671018169908421667955 23102506527254862632501933)
    ·
      refine ⟨8663439947720573487188225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23102506527254862632501933 8663439947720573487188225)
      ·
        refine ⟨6497579960790430115391169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8663439947720573487188225 6497579960790430115391169)
        ·
          refine ⟨4873184970592822586543377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6497579960790430115391169 4873184970592822586543377)
          ·
            refine ⟨3654888727944616939907533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4873184970592822586543377 3654888727944616939907533)
            ·
              refine ⟨1370583272979231352465325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3654888727944616939907533 1370583272979231352465325)
              ·
                refine ⟨513968727367211757174497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1370583272979231352465325 513968727367211757174497)
                ·
                  refine ⟨385476545525408817880873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513968727367211757174497 385476545525408817880873)
                  ·
                    rfl

theorem cell20_844552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_844552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844552 prefixEnd_844552 := by exact prefixLift 844552
  have htrace : WordTrace (prefixWord ++ tailWord_844552) baseStart_844552 baseEnd_844552 := by
    simpa [prefixWord, tailWord_844552, baseEnd_844552] using wordTrace_append hprefix tailTrace_844552
  have hstable : (prefixWord ++ tailWord_844552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844552).length < 2 ^ (prefixWord ++ tailWord_844552).sum := by decide
  have hdescent : baseEnd_844552 < baseStart_844552 := by decide
  rcases family_descends (prefixWord ++ tailWord_844552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844594 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_844594 : Nat := 118140960795 + 844594 * 2 ^ 59
def prefixEnd_844594 : Nat := 4983230072969 + 3 ^ 40 * 844594 * 2
def baseEnd_844594 : Nat := 385495715469843338480701

theorem tailTrace_844594 : CollatzResearch.WordTrace tailWord_844594 prefixEnd_844594 385495715469843338480701 := by
  unfold tailWord_844594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7701218475546914504091209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20536582601458438677576557 7701218475546914504091209)
  ·
    refine ⟨5775913856660185878068407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7701218475546914504091209 5775913856660185878068407)
    ·
      refine ⟨8663870784990278817102611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5775913856660185878068407 8663870784990278817102611)
      ·
        refine ⟨12995806177485418225653917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8663870784990278817102611 12995806177485418225653917)
        ·
          refine ⟨4873427316557031834620219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12995806177485418225653917 4873427316557031834620219)
          ·
            refine ⟨7310140974835547751930329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873427316557031834620219 7310140974835547751930329)
            ·
              refine ⟨5482605731126660813947747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7310140974835547751930329 5482605731126660813947747)
              ·
                refine ⟨8223908596689991220921621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5482605731126660813947747 8223908596689991220921621)
                ·
                  refine ⟨385495715469843338480701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8223908596689991220921621 385495715469843338480701)
                  ·
                    rfl

theorem cell20_844594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_844594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844594 prefixEnd_844594 := by exact prefixLift 844594
  have htrace : WordTrace (prefixWord ++ tailWord_844594) baseStart_844594 baseEnd_844594 := by
    simpa [prefixWord, tailWord_844594, baseEnd_844594] using wordTrace_append hprefix tailTrace_844594
  have hstable : (prefixWord ++ tailWord_844594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844594).length < 2 ^ (prefixWord ++ tailWord_844594).sum := by decide
  have hdescent : baseEnd_844594 < baseStart_844594 := by decide
  rcases family_descends (prefixWord ++ tailWord_844594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844608 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_844608 : Nat := 118140960795 + 844608 * 2 ^ 59
def prefixEnd_844608 : Nat := 4983230072969 + 3 ^ 40 * 844608 * 2
def baseEnd_844608 : Nat := 385502105451321512013977

theorem tailTrace_844608 : CollatzResearch.WordTrace tailWord_844608 prefixEnd_844608 385502105451321512013977 := by
  unfold tailWord_844608
  simp only [CollatzResearch.WordTrace]
  refine ⟨15402692262068469203687239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20536923016091292271582985 15402692262068469203687239)
  ·
    refine ⟨23104038393102703805530859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15402692262068469203687239 23104038393102703805530859)
    ·
      refine ⟨34656057589654055708296289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23104038393102703805530859 34656057589654055708296289)
      ·
        refine ⟨25992043192240541781222217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34656057589654055708296289 25992043192240541781222217)
        ·
          refine ⟨19494032394180406335916663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25992043192240541781222217 19494032394180406335916663)
          ·
            refine ⟨29241048591270609503874995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19494032394180406335916663 29241048591270609503874995)
            ·
              refine ⟨43861572886905914255812493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29241048591270609503874995 43861572886905914255812493)
              ·
                refine ⟨16448089832589717845929685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43861572886905914255812493 16448089832589717845929685)
                ·
                  refine ⟨385502105451321512013977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16448089832589717845929685 385502105451321512013977)
                  ·
                    rfl

theorem cell20_844608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_844608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844608 prefixEnd_844608 := by exact prefixLift 844608
  have htrace : WordTrace (prefixWord ++ tailWord_844608) baseStart_844608 baseEnd_844608 := by
    simpa [prefixWord, tailWord_844608, baseEnd_844608] using wordTrace_append hprefix tailTrace_844608
  have hstable : (prefixWord ++ tailWord_844608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844608).length < 2 ^ (prefixWord ++ tailWord_844608).sum := by decide
  have hdescent : baseEnd_844608 < baseStart_844608 := by decide
  rcases family_descends (prefixWord ++ tailWord_844608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844611 : List Nat := [1, 1, 1, 3, 1, 4, 2, 5, 2]
def baseStart_844611 : Nat := 118140960795 + 844611 * 2 ^ 59
def prefixEnd_844611 : Nat := 4983230072969 + 3 ^ 40 * 844611 * 2
def baseEnd_844611 : Nat := 385503474733066834913965

theorem tailTrace_844611 : CollatzResearch.WordTrace tailWord_844611 prefixEnd_844611 385503474733066834913965 := by
  unfold tailWord_844611
  simp only [CollatzResearch.WordTrace]
  refine ⟨30805493943126069919733687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20536995962084046613155791 30805493943126069919733687)
  ·
    refine ⟨46208240914689104879600531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30805493943126069919733687 46208240914689104879600531)
    ·
      refine ⟨69312361372033657319400797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46208240914689104879600531 69312361372033657319400797)
      ·
        refine ⟨25992135514512621494775299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69312361372033657319400797 25992135514512621494775299)
        ·
          refine ⟨38988203271768932242162949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25992135514512621494775299 38988203271768932242162949)
          ·
            refine ⟨7310288113456674795405553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38988203271768932242162949 7310288113456674795405553)
            ·
              refine ⟨5482716085092506096554165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7310288113456674795405553 5482716085092506096554165)
              ·
                refine ⟨514004632977422446551953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5482716085092506096554165 514004632977422446551953)
                ·
                  refine ⟨385503474733066834913965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514004632977422446551953 385503474733066834913965)
                  ·
                    rfl

theorem cell20_844611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 5, 2].length) (baseStart_844611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844611 prefixEnd_844611 := by exact prefixLift 844611
  have htrace : WordTrace (prefixWord ++ tailWord_844611) baseStart_844611 baseEnd_844611 := by
    simpa [prefixWord, tailWord_844611, baseEnd_844611] using wordTrace_append hprefix tailTrace_844611
  have hstable : (prefixWord ++ tailWord_844611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844611).length < 2 ^ (prefixWord ++ tailWord_844611).sum := by decide
  have hdescent : baseEnd_844611 < baseStart_844611 := by decide
  rcases family_descends (prefixWord ++ tailWord_844611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844614 : List Nat := [6, 1, 1, 2, 3, 7]
def baseStart_844614 : Nat := 118140960795 + 844614 * 2 ^ 59
def prefixEnd_844614 : Nat := 4983230072969 + 3 ^ 40 * 844614 * 2
def baseEnd_844614 : Nat := 14277957185733783622739

theorem tailTrace_844614 : CollatzResearch.WordTrace tailWord_844614 prefixEnd_844614 14277957185733783622739 := by
  unfold tailWord_844614
  simp only [CollatzResearch.WordTrace]
  refine ⟨962675105066100044752903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20537068908076800954728597 962675105066100044752903)
  ·
    refine ⟨1444012657599150067129355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962675105066100044752903 1444012657599150067129355)
    ·
      refine ⟨2166018986398725100694033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444012657599150067129355 2166018986398725100694033)
      ·
        refine ⟨1624514239799043825520525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2166018986398725100694033 1624514239799043825520525)
        ·
          refine ⟨609192839924641434570197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1624514239799043825520525 609192839924641434570197)
          ·
            refine ⟨14277957185733783622739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 609192839924641434570197 14277957185733783622739)
            ·
              rfl

theorem cell20_844614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 7].length) (baseStart_844614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844614 prefixEnd_844614 := by exact prefixLift 844614
  have htrace : WordTrace (prefixWord ++ tailWord_844614) baseStart_844614 baseEnd_844614 := by
    simpa [prefixWord, tailWord_844614, baseEnd_844614] using wordTrace_append hprefix tailTrace_844614
  have hstable : (prefixWord ++ tailWord_844614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844614).length < 2 ^ (prefixWord ++ tailWord_844614).sum := by decide
  have hdescent : baseEnd_844614 < baseStart_844614 := by decide
  rcases family_descends (prefixWord ++ tailWord_844614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844677 : List Nat := [1, 3, 1, 1, 3, 4, 7]
def baseStart_844677 : Nat := 118140960795 + 844677 * 2 ^ 59
def prefixEnd_844677 : Nat := 4983230072969 + 3 ^ 40 * 844677 * 2
def baseEnd_844677 : Nat := 42837066547940437634855

theorem tailTrace_844677 : CollatzResearch.WordTrace tailWord_844677 prefixEnd_844677 42837066547940437634855 := by
  unfold tailWord_844677
  simp only [CollatzResearch.WordTrace]
  refine ⟨30807901160886963191636285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20538600773924642127757523 30807901160886963191636285)
  ·
    refine ⟨11552962935332611196863607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30807901160886963191636285 11552962935332611196863607)
    ·
      refine ⟨17329444402998916795295411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11552962935332611196863607 17329444402998916795295411)
      ·
        refine ⟨25994166604498375192943117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17329444402998916795295411 25994166604498375192943117)
        ·
          refine ⟨9747812476686890697353669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25994166604498375192943117 9747812476686890697353669)
          ·
            refine ⟨1827714839378792005753813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9747812476686890697353669 1827714839378792005753813)
            ·
              refine ⟨42837066547940437634855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1827714839378792005753813 42837066547940437634855)
              ·
                rfl

theorem cell20_844677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 7].length) (baseStart_844677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844677 prefixEnd_844677 := by exact prefixLift 844677
  have htrace : WordTrace (prefixWord ++ tailWord_844677) baseStart_844677 baseEnd_844677 := by
    simpa [prefixWord, tailWord_844677, baseEnd_844677] using wordTrace_append hprefix tailTrace_844677
  have hstable : (prefixWord ++ tailWord_844677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844677).length < 2 ^ (prefixWord ++ tailWord_844677).sum := by decide
  have hdescent : baseEnd_844677 < baseStart_844677 := by decide
  rcases family_descends (prefixWord ++ tailWord_844677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844680 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_844680 : Nat := 118140960795 + 844680 * 2 ^ 59
def prefixEnd_844680 : Nat := 4983230072969 + 3 ^ 40 * 844680 * 2
def baseEnd_844680 : Nat := 385534968213209261613683

theorem tailTrace_844680 : CollatzResearch.WordTrace tailWord_844680 prefixEnd_844680 385534968213209261613683 := by
  unfold tailWord_844680
  simp only [CollatzResearch.WordTrace]
  refine ⟨15404005289938047351997747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20538673719917396469330329 15404005289938047351997747)
  ·
    refine ⟨23106007934907071027996621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15404005289938047351997747 23106007934907071027996621)
    ·
      refine ⟨8664752975590151635498733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23106007934907071027996621 8664752975590151635498733)
      ·
        refine ⟨3249282365846306863312025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8664752975590151635498733 3249282365846306863312025)
        ·
          refine ⟨2436961774384730147484019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3249282365846306863312025 2436961774384730147484019)
          ·
            refine ⟨3655442661577095221226029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436961774384730147484019 3655442661577095221226029)
            ·
              refine ⟨1370790998091410707959761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3655442661577095221226029 1370790998091410707959761)
              ·
                refine ⟨1028093248568558030969821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370790998091410707959761 1028093248568558030969821)
                ·
                  refine ⟨385534968213209261613683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028093248568558030969821 385534968213209261613683)
                  ·
                    rfl

theorem cell20_844680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_844680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844680 prefixEnd_844680 := by exact prefixLift 844680
  have htrace : WordTrace (prefixWord ++ tailWord_844680) baseStart_844680 baseEnd_844680 := by
    simpa [prefixWord, tailWord_844680, baseEnd_844680] using wordTrace_append hprefix tailTrace_844680
  have hstable : (prefixWord ++ tailWord_844680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844680).length < 2 ^ (prefixWord ++ tailWord_844680).sum := by decide
  have hdescent : baseEnd_844680 < baseStart_844680 := by decide
  rcases family_descends (prefixWord ++ tailWord_844680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844708 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_844708 : Nat := 118140960795 + 844708 * 2 ^ 59
def prefixEnd_844708 : Nat := 4983230072969 + 3 ^ 40 * 844708 * 2
def baseEnd_844708 : Nat := 385547748176165608680235

theorem tailTrace_844708 : CollatzResearch.WordTrace tailWord_844708 prefixEnd_844708 385547748176165608680235 := by
  unfold tailWord_844708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15404515911887327743007389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20539354549183103657343185 15404515911887327743007389)
  ·
    refine ⟨5776693466957747903627771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15404515911887327743007389 5776693466957747903627771)
    ·
      refine ⟨8665040200436621855441657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5776693466957747903627771 8665040200436621855441657)
      ·
        refine ⟨6498780150327466391581243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8665040200436621855441657 6498780150327466391581243)
        ·
          refine ⟨9748170225491199587371865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498780150327466391581243 9748170225491199587371865)
          ·
            refine ⟨7311127669118399690528899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9748170225491199587371865 7311127669118399690528899)
            ·
              refine ⟨10966691503677599535793349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7311127669118399690528899 10966691503677599535793349)
              ·
                refine ⟨2056254656939549912961253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10966691503677599535793349 2056254656939549912961253)
                ·
                  refine ⟨385547748176165608680235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2056254656939549912961253 385547748176165608680235)
                  ·
                    rfl

theorem cell20_844708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_844708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844708 prefixEnd_844708 := by exact prefixLift 844708
  have htrace : WordTrace (prefixWord ++ tailWord_844708) baseStart_844708 baseEnd_844708 := by
    simpa [prefixWord, tailWord_844708, baseEnd_844708] using wordTrace_append hprefix tailTrace_844708
  have hstable : (prefixWord ++ tailWord_844708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844708).length < 2 ^ (prefixWord ++ tailWord_844708).sum := by decide
  have hdescent : baseEnd_844708 < baseStart_844708 := by decide
  rcases family_descends (prefixWord ++ tailWord_844708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844717 : List Nat := [1, 5, 2, 3, 2, 1, 1, 3, 2]
def baseStart_844717 : Nat := 118140960795 + 844717 * 2 ^ 59
def prefixEnd_844717 : Nat := 4983230072969 + 3 ^ 40 * 844717 * 2
def baseEnd_844717 : Nat := 385551856021401577380199

theorem tailTrace_844717 : CollatzResearch.WordTrace tailWord_844717 prefixEnd_844717 385551856021401577380199 := by
  unfold tailWord_844717
  simp only [CollatzResearch.WordTrace]
  refine ⟨30809360080742050023092405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20539573387161366682061603 30809360080742050023092405)
  ·
    refine ⟨2888377507569567189664913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30809360080742050023092405 2888377507569567189664913)
    ·
      refine ⟨2166283130677175392248685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2888377507569567189664913 2166283130677175392248685)
      ·
        refine ⟨812356174003940772093257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2166283130677175392248685 812356174003940772093257)
        ·
          refine ⟨609267130502955579069943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812356174003940772093257 609267130502955579069943)
          ·
            refine ⟨913900695754433368604915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609267130502955579069943 913900695754433368604915)
            ·
              refine ⟨1370851043631650052907373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913900695754433368604915 1370851043631650052907373)
              ·
                refine ⟨514069141361868769840265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1370851043631650052907373 514069141361868769840265)
                ·
                  refine ⟨385551856021401577380199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514069141361868769840265 385551856021401577380199)
                  ·
                    rfl

theorem cell20_844717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_844717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844717 prefixEnd_844717 := by exact prefixLift 844717
  have htrace : WordTrace (prefixWord ++ tailWord_844717) baseStart_844717 baseEnd_844717 := by
    simpa [prefixWord, tailWord_844717, baseEnd_844717] using wordTrace_append hprefix tailTrace_844717
  have hstable : (prefixWord ++ tailWord_844717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844717).length < 2 ^ (prefixWord ++ tailWord_844717).sum := by decide
  have hdescent : baseEnd_844717 < baseStart_844717 := by decide
  rcases family_descends (prefixWord ++ tailWord_844717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844721 : List Nat := [1, 2, 2, 4, 3, 2, 1, 3, 2]
def baseStart_844721 : Nat := 118140960795 + 844721 * 2 ^ 59
def prefixEnd_844721 : Nat := 4983230072969 + 3 ^ 40 * 844721 * 2
def baseEnd_844721 : Nat := 385553681730395341246849

theorem tailTrace_844721 : CollatzResearch.WordTrace tailWord_844721 prefixEnd_844721 385553681730395341246849 := by
  unfold tailWord_844721
  simp only [CollatzResearch.WordTrace]
  refine ⟨30809505972727558706238017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20539670648485039137492011 30809505972727558706238017)
  ·
    refine ⟨23107129479545669029678513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30809505972727558706238017 23107129479545669029678513)
    ·
      refine ⟨17330347109659251772258885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23107129479545669029678513 17330347109659251772258885)
      ·
        refine ⟨3249440083061109707298541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17330347109659251772258885 3249440083061109707298541)
        ·
          refine ⟨1218540031147916140236953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3249440083061109707298541 1218540031147916140236953)
          ·
            refine ⟨913905023360937105177715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1218540031147916140236953 913905023360937105177715)
            ·
              refine ⟨1370857535041405657766573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913905023360937105177715 1370857535041405657766573)
              ·
                refine ⟨514071575640527121662465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1370857535041405657766573 514071575640527121662465)
                ·
                  refine ⟨385553681730395341246849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514071575640527121662465 385553681730395341246849)
                  ·
                    rfl

theorem cell20_844721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_844721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844721 prefixEnd_844721 := by exact prefixLift 844721
  have htrace : WordTrace (prefixWord ++ tailWord_844721) baseStart_844721 baseEnd_844721 := by
    simpa [prefixWord, tailWord_844721, baseEnd_844721] using wordTrace_append hprefix tailTrace_844721
  have hstable : (prefixWord ++ tailWord_844721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844721).length < 2 ^ (prefixWord ++ tailWord_844721).sum := by decide
  have hdescent : baseEnd_844721 < baseStart_844721 := by decide
  rcases family_descends (prefixWord ++ tailWord_844721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844753 : List Nat := [1, 2, 2, 1, 2, 1, 6, 5]
def baseStart_844753 : Nat := 118140960795 + 844753 * 2 ^ 59
def prefixEnd_844753 : Nat := 4983230072969 + 3 ^ 40 * 844753 * 2
def baseEnd_844753 : Nat := 128522762467448484060017

theorem tailTrace_844753 : CollatzResearch.WordTrace tailWord_844753 prefixEnd_844753 128522762467448484060017 := by
  unfold tailWord_844753
  simp only [CollatzResearch.WordTrace]
  refine ⟨30810673108611628171402913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20540448739074418780935275 30810673108611628171402913)
  ·
    refine ⟨23108004831458721128552185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30810673108611628171402913 23108004831458721128552185)
    ·
      refine ⟨17331003623594040846414139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23108004831458721128552185 17331003623594040846414139)
      ·
        refine ⟨25996505435391061269621209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17331003623594040846414139 25996505435391061269621209)
        ·
          refine ⟨19497379076543295952215907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25996505435391061269621209 19497379076543295952215907)
          ·
            refine ⟨29246068614814943928323861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19497379076543295952215907 29246068614814943928323861)
            ·
              refine ⟨1370909466319450496640181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29246068614814943928323861 1370909466319450496640181)
              ·
                refine ⟨128522762467448484060017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1370909466319450496640181 128522762467448484060017)
                ·
                  rfl

theorem cell20_844753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_844753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844753 prefixEnd_844753 := by exact prefixLift 844753
  have htrace : WordTrace (prefixWord ++ tailWord_844753) baseStart_844753 baseEnd_844753 := by
    simpa [prefixWord, tailWord_844753, baseEnd_844753] using wordTrace_append hprefix tailTrace_844753
  have hstable : (prefixWord ++ tailWord_844753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844753).length < 2 ^ (prefixWord ++ tailWord_844753).sum := by decide
  have hdescent : baseEnd_844753 < baseStart_844753 := by decide
  rcases family_descends (prefixWord ++ tailWord_844753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844756 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 3]
def baseStart_844756 : Nat := 118140960795 + 844756 * 2 ^ 59
def prefixEnd_844756 : Nat := 4983230072969 + 3 ^ 40 * 844756 * 2
def baseEnd_844756 : Nat := 385569656684090775080039

theorem tailTrace_844756 : CollatzResearch.WordTrace tailWord_844756 prefixEnd_844756 385569656684090775080039 := by
  unfold tailWord_844756
  simp only [CollatzResearch.WordTrace]
  refine ⟨15405391263800379841881061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20540521685067173122508081 15405391263800379841881061)
  ·
    refine ⟨2888510861962571220352699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15405391263800379841881061 2888510861962571220352699)
    ·
      refine ⟨4332766292943856830529049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2888510861962571220352699 4332766292943856830529049)
      ·
        refine ⟨3249574719707892622896787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4332766292943856830529049 3249574719707892622896787)
        ·
          refine ⟨4874362079561838934345181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3249574719707892622896787 4874362079561838934345181)
          ·
            refine ⟨1827885779835689600379443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4874362079561838934345181 1827885779835689600379443)
            ·
              refine ⟨2741828669753534400569165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827885779835689600379443 2741828669753534400569165)
              ·
                refine ⟨1028185751157575400213437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2741828669753534400569165 1028185751157575400213437)
                ·
                  refine ⟨385569656684090775080039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1028185751157575400213437 385569656684090775080039)
                  ·
                    rfl

theorem cell20_844756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_844756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844756 prefixEnd_844756 := by exact prefixLift 844756
  have htrace : WordTrace (prefixWord ++ tailWord_844756) baseStart_844756 baseEnd_844756 := by
    simpa [prefixWord, tailWord_844756, baseEnd_844756] using wordTrace_append hprefix tailTrace_844756
  have hstable : (prefixWord ++ tailWord_844756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844756).length < 2 ^ (prefixWord ++ tailWord_844756).sum := by decide
  have hdescent : baseEnd_844756 < baseStart_844756 := by decide
  rcases family_descends (prefixWord ++ tailWord_844756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844808 : List Nat := [2, 1, 3, 2, 1, 5, 1, 5]
def baseStart_844808 : Nat := 118140960795 + 844808 * 2 ^ 59
def prefixEnd_844808 : Nat := 4983230072969 + 3 ^ 40 * 844808 * 2
def baseEnd_844808 : Nat := 128531130300336568448831

theorem tailTrace_844808 : CollatzResearch.WordTrace tailWord_844808 prefixEnd_844808 128531130300336568448831 := by
  unfold tailWord_844808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15406339561706186282327539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20541786082274915043103385 15406339561706186282327539)
  ·
    refine ⟨23109509342559279423491309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15406339561706186282327539 23109509342559279423491309)
    ·
      refine ⟨8666066003459729783809241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23109509342559279423491309 8666066003459729783809241)
      ·
        refine ⟨6499549502594797337856931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8666066003459729783809241 6499549502594797337856931)
        ·
          refine ⟨9749324253892196006785397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6499549502594797337856931 9749324253892196006785397)
          ·
            refine ⟨913999148802393375636131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9749324253892196006785397 913999148802393375636131)
            ·
              refine ⟨1370998723203590063454197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913999148802393375636131 1370998723203590063454197)
              ·
                refine ⟨128531130300336568448831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1370998723203590063454197 128531130300336568448831)
                ·
                  rfl

theorem cell20_844808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_844808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844808 prefixEnd_844808 := by exact prefixLift 844808
  have htrace : WordTrace (prefixWord ++ tailWord_844808) baseStart_844808 baseEnd_844808 := by
    simpa [prefixWord, tailWord_844808, baseEnd_844808] using wordTrace_append hprefix tailTrace_844808
  have hstable : (prefixWord ++ tailWord_844808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844808).length < 2 ^ (prefixWord ++ tailWord_844808).sum := by decide
  have hdescent : baseEnd_844808 < baseStart_844808 := by decide
  rcases family_descends (prefixWord ++ tailWord_844808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844843 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_844843 : Nat := 118140960795 + 844843 * 2 ^ 59
def prefixEnd_844843 : Nat := 4983230072969 + 3 ^ 40 * 844843 * 2
def baseEnd_844843 : Nat := 385609365854705139179683

theorem tailTrace_844843 : CollatzResearch.WordTrace tailWord_844843 prefixEnd_844843 385609365854705139179683 := by
  unfold tailWord_844843
  simp only [CollatzResearch.WordTrace]
  refine ⟨30813955678285573542179183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20542637118857049028119455 30813955678285573542179183)
  ·
    refine ⟨46220933517428360313268775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30813955678285573542179183 46220933517428360313268775)
    ·
      refine ⟨69331400276142540469903163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46220933517428360313268775 69331400276142540469903163)
      ·
        refine ⟨103997100414213810704854745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69331400276142540469903163 103997100414213810704854745)
        ·
          refine ⟨77997825310660358028641059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103997100414213810704854745 77997825310660358028641059)
          ·
            refine ⟨116996737965990537042961589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77997825310660358028641059 116996737965990537042961589)
            ·
              refine ⟨10968444184311612847777649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116996737965990537042961589 10968444184311612847777649)
              ·
                refine ⟨8226333138233709635833237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10968444184311612847777649 8226333138233709635833237)
                ·
                  refine ⟨385609365854705139179683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8226333138233709635833237 385609365854705139179683)
                  ·
                    rfl

theorem cell20_844843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_844843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844843 prefixEnd_844843 := by exact prefixLift 844843
  have htrace : WordTrace (prefixWord ++ tailWord_844843) baseStart_844843 baseEnd_844843 := by
    simpa [prefixWord, tailWord_844843, baseEnd_844843] using wordTrace_append hprefix tailTrace_844843
  have hstable : (prefixWord ++ tailWord_844843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844843).length < 2 ^ (prefixWord ++ tailWord_844843).sum := by decide
  have hdescent : baseEnd_844843 < baseStart_844843 := by decide
  rcases family_descends (prefixWord ++ tailWord_844843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844860 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_844860 : Nat := 118140960795 + 844860 * 2 ^ 59
def prefixEnd_844860 : Nat := 4983230072969 + 3 ^ 40 * 844860 * 2
def baseEnd_844860 : Nat := 385617125117928635612947

theorem tailTrace_844860 : CollatzResearch.WordTrace tailWord_844860 prefixEnd_844860 385617125117928635612947 := by
  unfold tailWord_844860
  simp only [CollatzResearch.WordTrace]
  refine ⟨15407287859611992722774017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20543050479482656963698689 15407287859611992722774017)
  ·
    refine ⟨11555465894708994542080513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15407287859611992722774017 11555465894708994542080513)
    ·
      refine ⟨8666599421031745906560385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11555465894708994542080513 8666599421031745906560385)
      ·
        refine ⟨6499949565773809429920289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8666599421031745906560385 6499949565773809429920289)
        ·
          refine ⟨4874962174330357072440217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6499949565773809429920289 4874962174330357072440217)
          ·
            refine ⟨3656221630747767804330163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4874962174330357072440217 3656221630747767804330163)
            ·
              refine ⟨5484332446121651706495245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656221630747767804330163 5484332446121651706495245)
              ·
                refine ⟨2056624667295619389935717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5484332446121651706495245 2056624667295619389935717)
                ·
                  refine ⟨385617125117928635612947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2056624667295619389935717 385617125117928635612947)
                  ·
                    rfl

theorem cell20_844860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_844860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844860 prefixEnd_844860 := by exact prefixLift 844860
  have htrace : WordTrace (prefixWord ++ tailWord_844860) baseStart_844860 baseEnd_844860 := by
    simpa [prefixWord, tailWord_844860, baseEnd_844860] using wordTrace_append hprefix tailTrace_844860
  have hstable : (prefixWord ++ tailWord_844860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844860).length < 2 ^ (prefixWord ++ tailWord_844860).sum := by decide
  have hdescent : baseEnd_844860 < baseStart_844860 := by decide
  rcases family_descends (prefixWord ++ tailWord_844860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844877 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_844877 : Nat := 118140960795 + 844877 * 2 ^ 59
def prefixEnd_844877 : Nat := 4983230072969 + 3 ^ 40 * 844877 * 2
def baseEnd_844877 : Nat := 385624884381152132046211

theorem tailTrace_844877 : CollatzResearch.WordTrace tailWord_844877 prefixEnd_844877 385624884381152132046211 := by
  unfold tailWord_844877
  simp only [CollatzResearch.WordTrace]
  refine ⟨30815195760162397348916885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20543463840108264899277923 30815195760162397348916885)
  ·
    refine ⟨1444462301257612375730479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30815195760162397348916885 1444462301257612375730479)
    ·
      refine ⟨2166693451886418563595719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1444462301257612375730479 2166693451886418563595719)
      ·
        refine ⟨3250040177829627845393579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2166693451886418563595719 3250040177829627845393579)
        ·
          refine ⟨4875060266744441768090369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3250040177829627845393579 4875060266744441768090369)
          ·
            refine ⟨3656295200058331326067777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4875060266744441768090369 3656295200058331326067777)
            ·
              refine ⟨2742221400043748494550833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3656295200058331326067777 2742221400043748494550833)
              ·
                refine ⟨2056666050032811370913125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2742221400043748494550833 2056666050032811370913125)
                ·
                  refine ⟨385624884381152132046211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2056666050032811370913125 385624884381152132046211)
                  ·
                    rfl

theorem cell20_844877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_844877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844877 prefixEnd_844877 := by exact prefixLift 844877
  have htrace : WordTrace (prefixWord ++ tailWord_844877) baseStart_844877 baseEnd_844877 := by
    simpa [prefixWord, tailWord_844877, baseEnd_844877] using wordTrace_append hprefix tailTrace_844877
  have hstable : (prefixWord ++ tailWord_844877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844877).length < 2 ^ (prefixWord ++ tailWord_844877).sum := by decide
  have hdescent : baseEnd_844877 < baseStart_844877 := by decide
  rcases family_descends (prefixWord ++ tailWord_844877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844884 : List Nat := [2, 4, 1, 1, 1, 1, 6, 4]
def baseStart_844884 : Nat := 118140960795 + 844884 * 2 ^ 59
def prefixEnd_844884 : Nat := 4983230072969 + 3 ^ 40 * 844884 * 2
def baseEnd_844884 : Nat := 128542693123963739604283

theorem tailTrace_844884 : CollatzResearch.WordTrace tailWord_844884 prefixEnd_844884 128542693123963739604283 := by
  unfold tailWord_844884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15407725535568518772210853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20543634047424691696281137 15407725535568518772210853)
  ·
    refine ⟨2888948537919097269789535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15407725535568518772210853 2888948537919097269789535)
    ·
      refine ⟨4333422806878645904684303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2888948537919097269789535 4333422806878645904684303)
      ·
        refine ⟨6500134210317968857026455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4333422806878645904684303 6500134210317968857026455)
        ·
          refine ⟨9750201315476953285539683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6500134210317968857026455 9750201315476953285539683)
          ·
            refine ⟨14625301973215429928309525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9750201315476953285539683 14625301973215429928309525)
            ·
              refine ⟨685561029994473277889509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14625301973215429928309525 685561029994473277889509)
              ·
                refine ⟨128542693123963739604283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 685561029994473277889509 128542693123963739604283)
                ·
                  rfl

theorem cell20_844884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_844884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844884 prefixEnd_844884 := by exact prefixLift 844884
  have htrace : WordTrace (prefixWord ++ tailWord_844884) baseStart_844884 baseEnd_844884 := by
    simpa [prefixWord, tailWord_844884, baseEnd_844884] using wordTrace_append hprefix tailTrace_844884
  have hstable : (prefixWord ++ tailWord_844884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844884).length < 2 ^ (prefixWord ++ tailWord_844884).sum := by decide
  have hdescent : baseEnd_844884 < baseStart_844884 := by decide
  rcases family_descends (prefixWord ++ tailWord_844884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844905 : List Nat := [1, 2, 1, 1, 1, 8, 6]
def baseStart_844905 : Nat := 118140960795 + 844905 * 2 ^ 59
def prefixEnd_844905 : Nat := 4983230072969 + 3 ^ 40 * 844905 * 2
def baseEnd_844905 : Nat := 42848629371567608790307

theorem tailTrace_844905 : CollatzResearch.WordTrace tailWord_844905 prefixEnd_844905 42848629371567608790307 := by
  unfold tailWord_844905
  simp only [CollatzResearch.WordTrace]
  refine ⟨30816217004060958130936169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20544144669373972087290779 30816217004060958130936169)
  ·
    refine ⟨23112162753045718598202127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30816217004060958130936169 23112162753045718598202127)
    ·
      refine ⟨34668244129568577897303191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23112162753045718598202127 34668244129568577897303191)
      ·
        refine ⟨52002366194352866845954787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34668244129568577897303191 52002366194352866845954787)
        ·
          refine ⟨78003549291529300268932181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52002366194352866845954787 78003549291529300268932181)
          ·
            refine ⟨914104093260108987526549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 78003549291529300268932181 914104093260108987526549)
            ·
              refine ⟨42848629371567608790307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 914104093260108987526549 42848629371567608790307)
              ·
                rfl

theorem cell20_844905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 6].length) (baseStart_844905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844905 prefixEnd_844905 := by exact prefixLift 844905
  have htrace : WordTrace (prefixWord ++ tailWord_844905) baseStart_844905 baseEnd_844905 := by
    simpa [prefixWord, tailWord_844905, baseEnd_844905] using wordTrace_append hprefix tailTrace_844905
  have hstable : (prefixWord ++ tailWord_844905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844905).length < 2 ^ (prefixWord ++ tailWord_844905).sum := by decide
  have hdescent : baseEnd_844905 < baseStart_844905 := by decide
  rcases family_descends (prefixWord ++ tailWord_844905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_844912 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_844912 : Nat := 118140960795 + 844912 * 2 ^ 59
def prefixEnd_844912 : Nat := 4983230072969 + 3 ^ 40 * 844912 * 2
def baseEnd_844912 : Nat := 385640859334847565879401

theorem tailTrace_844912 : CollatzResearch.WordTrace tailWord_844912 prefixEnd_844912 385640859334847565879401 := by
  unfold tailWord_844912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15408236157517799163220495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20544314876690398884293993 15408236157517799163220495)
  ·
    refine ⟨23112354236276698744830743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15408236157517799163220495 23112354236276698744830743)
    ·
      refine ⟨34668531354415048117246115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23112354236276698744830743 34668531354415048117246115)
      ·
        refine ⟨52002797031622572175869173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34668531354415048117246115 52002797031622572175869173)
        ·
          refine ⟨4875262221714616141487735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52002797031622572175869173 4875262221714616141487735)
          ·
            refine ⟨7312893332571924212231603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4875262221714616141487735 7312893332571924212231603)
            ·
              refine ⟨10969339998857886318347405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312893332571924212231603 10969339998857886318347405)
              ·
                refine ⟨4113502499571707369380277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10969339998857886318347405 4113502499571707369380277)
                ·
                  refine ⟨385640859334847565879401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4113502499571707369380277 385640859334847565879401)
                  ·
                    rfl

theorem cell20_844912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_844912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_844912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_844912 prefixEnd_844912 := by exact prefixLift 844912
  have htrace : WordTrace (prefixWord ++ tailWord_844912) baseStart_844912 baseEnd_844912 := by
    simpa [prefixWord, tailWord_844912, baseEnd_844912] using wordTrace_append hprefix tailTrace_844912
  have hstable : (prefixWord ++ tailWord_844912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_844912).length < 2 ^ (prefixWord ++ tailWord_844912).sum := by decide
  have hdescent : baseEnd_844912 < baseStart_844912 := by decide
  rcases family_descends (prefixWord ++ tailWord_844912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
