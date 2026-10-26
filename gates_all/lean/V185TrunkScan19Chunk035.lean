import V185TrunkScan19Chunk034

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_351474 : List Nat := [3, 2, 1, 3, 4, 1, 5]
def baseStart_351474 : Nat := 118140960795 + 351474 * 2 ^ 59
def prefixEnd_351474 : Nat := 4983230072969 + 3 ^ 40 * 351474 * 2
def baseEnd_351474 : Nat := 35649402381918635073305

theorem tailTrace_351474 : CollatzResearch.WordTrace tailWord_351474 prefixEnd_351474 35649402381918635073305 := by
  unfold tailWord_351474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204827482169299956329369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8546206619118133216878317 3204827482169299956329369)
  ·
    refine ⟨2403620611626974967247027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3204827482169299956329369 2403620611626974967247027)
    ·
      refine ⟨3605430917440462450870541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2403620611626974967247027 3605430917440462450870541)
      ·
        refine ⟨1352036594040173419076453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3605430917440462450870541 1352036594040173419076453)
        ·
          refine ⟨253506861382532516076835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1352036594040173419076453 253506861382532516076835)
          ·
            refine ⟨380260292073798774115253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253506861382532516076835 380260292073798774115253)
            ·
              refine ⟨35649402381918635073305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 380260292073798774115253 35649402381918635073305)
              ·
                rfl

theorem cell19_351474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 5].length) (baseStart_351474 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351474 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351474 prefixEnd_351474 := by exact prefixLift 351474
  have htrace : WordTrace (prefixWord ++ tailWord_351474) baseStart_351474 baseEnd_351474 := by
    simpa [prefixWord, tailWord_351474, baseEnd_351474] using wordTrace_append hprefix tailTrace_351474
  have hstable : (prefixWord ++ tailWord_351474).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351474).length < 2 ^ (prefixWord ++ tailWord_351474).sum := by decide
  have hdescent : baseEnd_351474 < baseStart_351474 := by decide
  rcases family_descends (prefixWord ++ tailWord_351474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351497 : List Nat := [1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_351497 : Nat := 118140960795 + 351497 * 2 ^ 59
def prefixEnd_351497 : Nat := 4983230072969 + 3 ^ 40 * 351497 * 2
def baseEnd_351497 : Nat := 106955205696898666708741

theorem tailTrace_351497 : CollatzResearch.WordTrace tailWord_351497 prefixEnd_351497 106955205696898666708741 := by
  unfold tailWord_351497
  simp only [CollatzResearch.WordTrace]
  refine ⟨12820148807593874753404745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8546765871729249835603163 12820148807593874753404745)
  ·
    refine ⟨9615111605695406065053559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12820148807593874753404745 9615111605695406065053559)
    ·
      refine ⟨14422667408543109097580339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9615111605695406065053559 14422667408543109097580339)
      ·
        refine ⟨21634001112814663646370509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14422667408543109097580339 21634001112814663646370509)
        ·
          refine ⟨8112750417305498867388941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21634001112814663646370509 8112750417305498867388941)
          ·
            refine ⟨3042281406489562075270853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8112750417305498867388941 3042281406489562075270853)
            ·
              refine ⟨570427763716792889113285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3042281406489562075270853 570427763716792889113285)
              ·
                refine ⟨106955205696898666708741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 570427763716792889113285 106955205696898666708741)
                ·
                  rfl

theorem cell19_351497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_351497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351497 prefixEnd_351497 := by exact prefixLift 351497
  have htrace : WordTrace (prefixWord ++ tailWord_351497) baseStart_351497 baseEnd_351497 := by
    simpa [prefixWord, tailWord_351497, baseEnd_351497] using wordTrace_append hprefix tailTrace_351497
  have hstable : (prefixWord ++ tailWord_351497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351497).length < 2 ^ (prefixWord ++ tailWord_351497).sum := by decide
  have hdescent : baseEnd_351497 < baseStart_351497 := by decide
  rcases family_descends (prefixWord ++ tailWord_351497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351516 : List Nat := [2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_351516 : Nat := 118140960795 + 351516 * 2 ^ 59
def prefixEnd_351516 : Nat := 4983230072969 + 3 ^ 40 * 351516 * 2
def baseEnd_351516 : Nat := 106960987108712252286467

theorem tailTrace_351516 : CollatzResearch.WordTrace tailWord_351516 prefixEnd_351516 106960987108712252286467 := by
  unfold tailWord_351516
  simp only [CollatzResearch.WordTrace]
  refine ⟨6410420897262520499173201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8547227863016693998897601 6410420897262520499173201)
  ·
    refine ⟨4807815672946890374379901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6410420897262520499173201 4807815672946890374379901)
    ·
      refine ⟨1802930877355083890392463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4807815672946890374379901 1802930877355083890392463)
      ·
        refine ⟨2704396316032625835588695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802930877355083890392463 2704396316032625835588695)
        ·
          refine ⟨4056594474048938753383043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704396316032625835588695 4056594474048938753383043)
          ·
            refine ⟨6084891711073408130074565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4056594474048938753383043 6084891711073408130074565)
            ·
              refine ⟨1140917195826264024388981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6084891711073408130074565 1140917195826264024388981)
              ·
                refine ⟨106960987108712252286467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1140917195826264024388981 106960987108712252286467)
                ·
                  rfl

theorem cell19_351516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_351516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351516 prefixEnd_351516 := by exact prefixLift 351516
  have htrace : WordTrace (prefixWord ++ tailWord_351516) baseStart_351516 baseEnd_351516 := by
    simpa [prefixWord, tailWord_351516, baseEnd_351516] using wordTrace_append hprefix tailTrace_351516
  have hstable : (prefixWord ++ tailWord_351516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351516).length < 2 ^ (prefixWord ++ tailWord_351516).sum := by decide
  have hdescent : baseEnd_351516 < baseStart_351516 := by decide
  rcases family_descends (prefixWord ++ tailWord_351516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351533 : List Nat := [1, 5, 3, 1, 1, 8]
def baseStart_351533 : Nat := 118140960795 + 351533 * 2 ^ 59
def prefixEnd_351533 : Nat := 4983230072969 + 3 ^ 40 * 351533 * 2
def baseEnd_351533 : Nat := 11885128883429027767627

theorem tailTrace_351533 : CollatzResearch.WordTrace tailWord_351533 prefixEnd_351533 11885128883429027767627 := by
  unfold tailWord_351533
  simp only [CollatzResearch.WordTrace]
  refine ⟨12821461835463452901715253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8547641223642301934476835 12821461835463452901715253)
  ·
    refine ⟨1202012047074698709535805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12821461835463452901715253 1202012047074698709535805)
    ·
      refine ⟨450754517653012016075927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1202012047074698709535805 450754517653012016075927)
      ·
        refine ⟨676131776479518024113891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450754517653012016075927 676131776479518024113891)
        ·
          refine ⟨1014197664719277036170837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676131776479518024113891 1014197664719277036170837)
          ·
            refine ⟨11885128883429027767627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1014197664719277036170837 11885128883429027767627)
            ·
              rfl

theorem cell19_351533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 8].length) (baseStart_351533 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351533 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351533 prefixEnd_351533 := by exact prefixLift 351533
  have htrace : WordTrace (prefixWord ++ tailWord_351533) baseStart_351533 baseEnd_351533 := by
    simpa [prefixWord, tailWord_351533, baseEnd_351533] using wordTrace_append hprefix tailTrace_351533
  have hstable : (prefixWord ++ tailWord_351533).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351533).length < 2 ^ (prefixWord ++ tailWord_351533).sum := by decide
  have hdescent : baseEnd_351533 < baseStart_351533 := by decide
  rcases family_descends (prefixWord ++ tailWord_351533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351708 : List Nat := [2, 2, 15]
def baseStart_351708 : Nat := 118140960795 + 351708 * 2 ^ 59
def prefixEnd_351708 : Nat := 4983230072969 + 3 ^ 40 * 351708 * 2
def baseEnd_351708 : Nat := 440409093812809448639

theorem tailTrace_351708 : CollatzResearch.WordTrace tailWord_351708 prefixEnd_351708 440409093812809448639 := by
  unfold tailWord_351708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6413922304914728894667889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8551896406552971859557185 6413922304914728894667889)
  ·
    refine ⟨4810441728686046671000917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6413922304914728894667889 4810441728686046671000917)
    ·
      refine ⟨440409093812809448639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 4810441728686046671000917 440409093812809448639)
      ·
        rfl

theorem cell19_351708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 15].length) (baseStart_351708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351708 prefixEnd_351708 := by exact prefixLift 351708
  have htrace : WordTrace (prefixWord ++ tailWord_351708) baseStart_351708 baseEnd_351708 := by
    simpa [prefixWord, tailWord_351708, baseEnd_351708] using wordTrace_append hprefix tailTrace_351708
  have hstable : (prefixWord ++ tailWord_351708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351708).length < 2 ^ (prefixWord ++ tailWord_351708).sum := by decide
  have hdescent : baseEnd_351708 < baseStart_351708 := by decide
  rcases family_descends (prefixWord ++ tailWord_351708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351799 : List Nat := [1, 1, 3, 1, 2, 6, 2, 3]
def baseStart_351799 : Nat := 118140960795 + 351799 * 2 ^ 59
def prefixEnd_351799 : Nat := 4983230072969 + 3 ^ 40 * 351799 * 2
def baseEnd_351799 : Nat := 107047099716251447996807

theorem tailTrace_351799 : CollatzResearch.WordTrace tailWord_351799 prefixEnd_351799 107047099716251447996807 := by
  unfold tailWord_351799
  simp only [CollatzResearch.WordTrace]
  refine ⟨12831163652499780330898451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8554109101666520220598967 12831163652499780330898451)
  ·
    refine ⟨19246745478749670496347677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12831163652499780330898451 19246745478749670496347677)
    ·
      refine ⟨7217529554531126436130379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19246745478749670496347677 7217529554531126436130379)
      ·
        refine ⟨10826294331796689654195569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7217529554531126436130379 10826294331796689654195569)
        ·
          refine ⟨8119720748847517240646677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10826294331796689654195569 8119720748847517240646677)
          ·
            refine ⟨380611910102227370655313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8119720748847517240646677 380611910102227370655313)
            ·
              refine ⟨285458932576670527991485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380611910102227370655313 285458932576670527991485)
              ·
                refine ⟨107047099716251447996807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285458932576670527991485 107047099716251447996807)
                ·
                  rfl

theorem cell19_351799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 3].length) (baseStart_351799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351799 prefixEnd_351799 := by exact prefixLift 351799
  have htrace : WordTrace (prefixWord ++ tailWord_351799) baseStart_351799 baseEnd_351799 := by
    simpa [prefixWord, tailWord_351799, baseEnd_351799] using wordTrace_append hprefix tailTrace_351799
  have hstable : (prefixWord ++ tailWord_351799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351799).length < 2 ^ (prefixWord ++ tailWord_351799).sum := by decide
  have hdescent : baseEnd_351799 < baseStart_351799 := by decide
  rcases family_descends (prefixWord ++ tailWord_351799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351801 : List Nat := [1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_351801 : Nat := 118140960795 + 351801 * 2 ^ 59
def prefixEnd_351801 : Nat := 4983230072969 + 3 ^ 40 * 351801 * 2
def baseEnd_351801 : Nat := 107047708285916035952357

theorem tailTrace_351801 : CollatzResearch.WordTrace tailWord_351801 prefixEnd_351801 107047708285916035952357 := by
  unfold tailWord_351801
  simp only [CollatzResearch.WordTrace]
  refine ⟨12831236598492534672471257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8554157732328356448314171 12831236598492534672471257)
  ·
    refine ⟨9623427448869401004353443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12831236598492534672471257 9623427448869401004353443)
    ·
      refine ⟨14435141173304101506530165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9623427448869401004353443 14435141173304101506530165)
      ·
        refine ⟨1353294484997259516237203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14435141173304101506530165 1353294484997259516237203)
        ·
          refine ⟨2029941727495889274355805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353294484997259516237203 2029941727495889274355805)
          ·
            refine ⟨761228147810958477883427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2029941727495889274355805 761228147810958477883427)
            ·
              refine ⟨1141842221716437716825141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761228147810958477883427 1141842221716437716825141)
              ·
                refine ⟨107047708285916035952357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1141842221716437716825141 107047708285916035952357)
                ·
                  rfl

theorem cell19_351801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_351801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351801 prefixEnd_351801 := by exact prefixLift 351801
  have htrace : WordTrace (prefixWord ++ tailWord_351801) baseStart_351801 baseEnd_351801 := by
    simpa [prefixWord, tailWord_351801, baseEnd_351801] using wordTrace_append hprefix tailTrace_351801
  have hstable : (prefixWord ++ tailWord_351801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351801).length < 2 ^ (prefixWord ++ tailWord_351801).sum := by decide
  have hdescent : baseEnd_351801 < baseStart_351801 := by decide
  rcases family_descends (prefixWord ++ tailWord_351801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351814 : List Nat := [6, 1, 1, 1, 4, 1, 5]
def baseStart_351814 : Nat := 118140960795 + 351814 * 2 ^ 59
def prefixEnd_351814 : Nat := 4983230072969 + 3 ^ 40 * 351814 * 2
def baseEnd_351814 : Nat := 35683887996245285887811

theorem tailTrace_351814 : CollatzResearch.WordTrace tailWord_351814 prefixEnd_351814 35683887996245285887811 := by
  unfold tailWord_351814
  simp only [CollatzResearch.WordTrace]
  refine ⟨400990960857669934146703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8554473831630291928462997 400990960857669934146703)
  ·
    refine ⟨601486441286504901220055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 400990960857669934146703 601486441286504901220055)
    ·
      refine ⟨902229661929757351830083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 601486441286504901220055 902229661929757351830083)
      ·
        refine ⟨1353344492894636027745125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902229661929757351830083 1353344492894636027745125)
        ·
          refine ⟨253752092417744255202211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1353344492894636027745125 253752092417744255202211)
          ·
            refine ⟨380628138626616382803317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253752092417744255202211 380628138626616382803317)
            ·
              refine ⟨35683887996245285887811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 380628138626616382803317 35683887996245285887811)
              ·
                rfl

theorem cell19_351814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 5].length) (baseStart_351814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351814 prefixEnd_351814 := by exact prefixLift 351814
  have htrace : WordTrace (prefixWord ++ tailWord_351814) baseStart_351814 baseEnd_351814 := by
    simpa [prefixWord, tailWord_351814, baseEnd_351814] using wordTrace_append hprefix tailTrace_351814
  have hstable : (prefixWord ++ tailWord_351814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351814).length < 2 ^ (prefixWord ++ tailWord_351814).sum := by decide
  have hdescent : baseEnd_351814 < baseStart_351814 := by decide
  rcases family_descends (prefixWord ++ tailWord_351814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351820 : List Nat := [2, 2, 1, 3, 1, 5, 5]
def baseStart_351820 : Nat := 118140960795 + 351820 * 2 ^ 59
def prefixEnd_351820 : Nat := 4983230072969 + 3 ^ 40 * 351820 * 2
def baseEnd_351820 : Nat := 35684496565909873843361

theorem tailTrace_351820 : CollatzResearch.WordTrace tailWord_351820 prefixEnd_351820 35684496565909873843361 := by
  unfold tailWord_351820
  simp only [CollatzResearch.WordTrace]
  refine ⟨6415964792711850458706457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8554619723615800611608609 6415964792711850458706457)
  ·
    refine ⟨4811973594533887844029843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6415964792711850458706457 4811973594533887844029843)
    ·
      refine ⟨7217960391800831766044765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4811973594533887844029843 7217960391800831766044765)
      ·
        refine ⟨2706735146925311912266787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7217960391800831766044765 2706735146925311912266787)
        ·
          refine ⟨4060102720387967868400181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706735146925311912266787 4060102720387967868400181)
          ·
            refine ⟨380634630036371987662517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4060102720387967868400181 380634630036371987662517)
            ·
              refine ⟨35684496565909873843361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 380634630036371987662517 35684496565909873843361)
              ·
                rfl

theorem cell19_351820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_351820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351820 prefixEnd_351820 := by exact prefixLift 351820
  have htrace : WordTrace (prefixWord ++ tailWord_351820) baseStart_351820 baseEnd_351820 := by
    simpa [prefixWord, tailWord_351820, baseEnd_351820] using wordTrace_append hprefix tailTrace_351820
  have hstable : (prefixWord ++ tailWord_351820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351820).length < 2 ^ (prefixWord ++ tailWord_351820).sum := by decide
  have hdescent : baseEnd_351820 < baseStart_351820 := by decide
  rcases family_descends (prefixWord ++ tailWord_351820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351858 : List Nat := [3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_351858 : Nat := 118140960795 + 351858 * 2 ^ 59
def prefixEnd_351858 : Nat := 4983230072969 + 3 ^ 40 * 351858 * 2
def baseEnd_351858 : Nat := 107065052521356792685535

theorem tailTrace_351858 : CollatzResearch.WordTrace tailWord_351858 prefixEnd_351858 107065052521356792685535 := by
  unfold tailWord_351858
  simp only [CollatzResearch.WordTrace]
  refine ⟨3208328889821508351824057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8555543706190688938197485 3208328889821508351824057)
  ·
    refine ⟨2406246667366131263868043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3208328889821508351824057 2406246667366131263868043)
    ·
      refine ⟨3609370001049196895802065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2406246667366131263868043 3609370001049196895802065)
      ·
        refine ⟨2707027500786897671851549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3609370001049196895802065 2707027500786897671851549)
        ·
          refine ⟨1015135312795086626944331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2707027500786897671851549 1015135312795086626944331)
          ·
            refine ⟨1522702969192629940416497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015135312795086626944331 1522702969192629940416497)
            ·
              refine ⟨1142027226894472455312373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1522702969192629940416497 1142027226894472455312373)
              ·
                refine ⟨107065052521356792685535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1142027226894472455312373 107065052521356792685535)
                ·
                  rfl

theorem cell19_351858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_351858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351858 prefixEnd_351858 := by exact prefixLift 351858
  have htrace : WordTrace (prefixWord ++ tailWord_351858) baseStart_351858 baseEnd_351858 := by
    simpa [prefixWord, tailWord_351858, baseEnd_351858] using wordTrace_append hprefix tailTrace_351858
  have hstable : (prefixWord ++ tailWord_351858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351858).length < 2 ^ (prefixWord ++ tailWord_351858).sum := by decide
  have hdescent : baseEnd_351858 < baseStart_351858 := by decide
  rcases family_descends (prefixWord ++ tailWord_351858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351879 : List Nat := [1, 1, 4, 2, 1, 10]
def baseStart_351879 : Nat := 118140960795 + 351879 * 2 ^ 59
def prefixEnd_351879 : Nat := 4983230072969 + 3 ^ 40 * 351879 * 2
def baseEnd_351879 : Nat := 11896826944759440690979

theorem tailTrace_351879 : CollatzResearch.WordTrace tailWord_351879 prefixEnd_351879 11896826944759440690979 := by
  unfold tailWord_351879
  simp only [CollatzResearch.WordTrace]
  refine ⟨12834081492209953993810691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8556054328139969329207127 12834081492209953993810691)
  ·
    refine ⟨19251122238314930990716037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12834081492209953993810691 19251122238314930990716037)
    ·
      refine ⟨3609585419684049560759257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19251122238314930990716037 3609585419684049560759257)
      ·
        refine ⟨2707189064763037170569443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3609585419684049560759257 2707189064763037170569443)
        ·
          refine ⟨4060783597144555755854165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707189064763037170569443 4060783597144555755854165)
          ·
            refine ⟨11896826944759440690979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4060783597144555755854165 11896826944759440690979)
            ·
              rfl

theorem cell19_351879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 10].length) (baseStart_351879 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351879 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351879 prefixEnd_351879 := by exact prefixLift 351879
  have htrace : WordTrace (prefixWord ++ tailWord_351879) baseStart_351879 baseEnd_351879 := by
    simpa [prefixWord, tailWord_351879, baseEnd_351879] using wordTrace_append hprefix tailTrace_351879
  have hstable : (prefixWord ++ tailWord_351879).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351879).length < 2 ^ (prefixWord ++ tailWord_351879).sum := by decide
  have hdescent : baseEnd_351879 < baseStart_351879 := by decide
  rcases family_descends (prefixWord ++ tailWord_351879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351892 : List Nat := [2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_351892 : Nat := 118140960795 + 351892 * 2 ^ 59
def prefixEnd_351892 : Nat := 4983230072969 + 3 ^ 40 * 351892 * 2
def baseEnd_351892 : Nat := 107075398205654787929887

theorem tailTrace_351892 : CollatzResearch.WordTrace tailWord_351892 prefixEnd_351892 107075398205654787929887 := by
  unfold tailWord_351892
  simp only [CollatzResearch.WordTrace]
  refine ⟨6417277820581428607016965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8556370427441904809355953 6417277820581428607016965)
  ·
    refine ⟨1203239591359017863815681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6417277820581428607016965 1203239591359017863815681)
    ·
      refine ⟨902429693519263397861761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1203239591359017863815681 902429693519263397861761)
      ·
        refine ⟨676822270139447548396321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 902429693519263397861761 676822270139447548396321)
        ·
          refine ⟨507616702604585661297241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676822270139447548396321 507616702604585661297241)
          ·
            refine ⟨380712526953439245972931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507616702604585661297241 380712526953439245972931)
            ·
              refine ⟨571068790430158868959397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380712526953439245972931 571068790430158868959397)
              ·
                refine ⟨107075398205654787929887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571068790430158868959397 107075398205654787929887)
                ·
                  rfl

theorem cell19_351892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_351892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351892 prefixEnd_351892 := by exact prefixLift 351892
  have htrace : WordTrace (prefixWord ++ tailWord_351892) baseStart_351892 baseEnd_351892 := by
    simpa [prefixWord, tailWord_351892, baseEnd_351892] using wordTrace_append hprefix tailTrace_351892
  have hstable : (prefixWord ++ tailWord_351892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351892).length < 2 ^ (prefixWord ++ tailWord_351892).sum := by decide
  have hdescent : baseEnd_351892 < baseStart_351892 := by decide
  rcases family_descends (prefixWord ++ tailWord_351892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351896 : List Nat := [2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_351896 : Nat := 118140960795 + 351896 * 2 ^ 59
def prefixEnd_351896 : Nat := 4983230072969 + 3 ^ 40 * 351896 * 2
def baseEnd_351896 : Nat := 107076615344983963840987

theorem tailTrace_351896 : CollatzResearch.WordTrace tailWord_351896 prefixEnd_351896 107076615344983963840987 := by
  unfold tailWord_351896
  simp only [CollatzResearch.WordTrace]
  refine ⟨6417350766574182948589771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8556467688765577264786361 6417350766574182948589771)
  ·
    refine ⟨9626026149861274422884657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6417350766574182948589771 9626026149861274422884657)
    ·
      refine ⟨7219519612395955817163493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9626026149861274422884657 7219519612395955817163493)
      ·
        refine ⟨1353659927324241715718155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7219519612395955817163493 1353659927324241715718155)
        ·
          refine ⟨2030489890986362573577233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353659927324241715718155 2030489890986362573577233)
          ·
            refine ⟨1522867418239771930182925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2030489890986362573577233 1522867418239771930182925)
            ·
              refine ⟨571075281839914473818597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1522867418239771930182925 571075281839914473818597)
              ·
                refine ⟨107076615344983963840987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571075281839914473818597 107076615344983963840987)
                ·
                  rfl

theorem cell19_351896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_351896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351896 prefixEnd_351896 := by exact prefixLift 351896
  have htrace : WordTrace (prefixWord ++ tailWord_351896) baseStart_351896 baseEnd_351896 := by
    simpa [prefixWord, tailWord_351896, baseEnd_351896] using wordTrace_append hprefix tailTrace_351896
  have hstable : (prefixWord ++ tailWord_351896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351896).length < 2 ^ (prefixWord ++ tailWord_351896).sum := by decide
  have hdescent : baseEnd_351896 < baseStart_351896 := by decide
  rcases family_descends (prefixWord ++ tailWord_351896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351934 : List Nat := [4, 2, 1, 1, 2, 3, 6]
def baseStart_351934 : Nat := 118140960795 + 351934 * 2 ^ 59
def prefixEnd_351934 : Nat := 4983230072969 + 3 ^ 40 * 351934 * 2
def baseEnd_351934 : Nat := 35696059389537044998813

theorem tailTrace_351934 : CollatzResearch.WordTrace tailWord_351934 prefixEnd_351934 35696059389537044998813 := by
  unfold tailWord_351934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604510938376337298382857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8557391671340465591375237 1604510938376337298382857)
  ·
    refine ⟨1203383203782252973787143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1604510938376337298382857 1203383203782252973787143)
    ·
      refine ⟨1805074805673379460680715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203383203782252973787143 1805074805673379460680715)
      ·
        refine ⟨2707612208510069191021073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805074805673379460680715 2707612208510069191021073)
        ·
          refine ⟨2030709156382551893265805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2707612208510069191021073 2030709156382551893265805)
          ·
            refine ⟨761515933643456959974677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2030709156382551893265805 761515933643456959974677)
            ·
              refine ⟨35696059389537044998813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 761515933643456959974677 35696059389537044998813)
              ·
                rfl

theorem cell19_351934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_351934 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351934 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351934 prefixEnd_351934 := by exact prefixLift 351934
  have htrace : WordTrace (prefixWord ++ tailWord_351934) baseStart_351934 baseEnd_351934 := by
    simpa [prefixWord, tailWord_351934, baseEnd_351934] using wordTrace_append hprefix tailTrace_351934
  have hstable : (prefixWord ++ tailWord_351934).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351934).length < 2 ^ (prefixWord ++ tailWord_351934).sum := by decide
  have hdescent : baseEnd_351934 < baseStart_351934 := by decide
  rcases family_descends (prefixWord ++ tailWord_351934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351936 : List Nat := [2, 1, 1, 2, 4, 1, 8]
def baseStart_351936 : Nat := 118140960795 + 351936 * 2 ^ 59
def prefixEnd_351936 : Nat := 4983230072969 + 3 ^ 40 * 351936 * 2
def baseEnd_351936 : Nat := 35696262246091907650663

theorem tailTrace_351936 : CollatzResearch.WordTrace tailWord_351936 prefixEnd_351936 35696262246091907650663 := by
  unfold tailWord_351936
  simp only [CollatzResearch.WordTrace]
  refine ⟨6418080226501726364317831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8557440302002301819090441 6418080226501726364317831)
  ·
    refine ⟨9627120339752589546476747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6418080226501726364317831 9627120339752589546476747)
    ·
      refine ⟨14440680509628884319715121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9627120339752589546476747 14440680509628884319715121)
      ·
        refine ⟨10830510382221663239786341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14440680509628884319715121 10830510382221663239786341)
        ·
          refine ⟨2030720696666561857459939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10830510382221663239786341 2030720696666561857459939)
          ·
            refine ⟨3046081044999842786189909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030720696666561857459939 3046081044999842786189909)
            ·
              refine ⟨35696262246091907650663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3046081044999842786189909 35696262246091907650663)
              ·
                rfl

theorem cell19_351936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_351936 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_351936 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_351936 prefixEnd_351936 := by exact prefixLift 351936
  have htrace : WordTrace (prefixWord ++ tailWord_351936) baseStart_351936 baseEnd_351936 := by
    simpa [prefixWord, tailWord_351936, baseEnd_351936] using wordTrace_append hprefix tailTrace_351936
  have hstable : (prefixWord ++ tailWord_351936).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351936).length < 2 ^ (prefixWord ++ tailWord_351936).sum := by decide
  have hdescent : baseEnd_351936 < baseStart_351936 := by decide
  rcases family_descends (prefixWord ++ tailWord_351936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352010 : List Nat := [3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_352010 : Nat := 118140960795 + 352010 * 2 ^ 59
def prefixEnd_352010 : Nat := 4983230072969 + 3 ^ 40 * 352010 * 2
def baseEnd_352010 : Nat := 107111303815865477307343

theorem tailTrace_352010 : CollatzResearch.WordTrace tailWord_352010 prefixEnd_352010 107111303815865477307343 := by
  unfold tailWord_352010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3209714863683840841707371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8559239636490242244552989 3209714863683840841707371)
  ·
    refine ⟨4814572295525761262561057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3209714863683840841707371 4814572295525761262561057)
    ·
      refine ⟨3610929221644320946920793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4814572295525761262561057 3610929221644320946920793)
      ·
        refine ⟨2708196916233240710190595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3610929221644320946920793 2708196916233240710190595)
        ·
          refine ⟨4062295374349861065285893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708196916233240710190595 4062295374349861065285893)
          ·
            refine ⟨761680382690598949741105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4062295374349861065285893 761680382690598949741105)
            ·
              refine ⟨571260287017949212305829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 761680382690598949741105 571260287017949212305829)
              ·
                refine ⟨107111303815865477307343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571260287017949212305829 107111303815865477307343)
                ·
                  rfl

theorem cell19_352010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_352010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352010 prefixEnd_352010 := by exact prefixLift 352010
  have htrace : WordTrace (prefixWord ++ tailWord_352010) baseStart_352010 baseEnd_352010 := by
    simpa [prefixWord, tailWord_352010, baseEnd_352010] using wordTrace_append hprefix tailTrace_352010
  have hstable : (prefixWord ++ tailWord_352010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352010).length < 2 ^ (prefixWord ++ tailWord_352010).sum := by decide
  have hdescent : baseEnd_352010 < baseStart_352010 := by decide
  rcases family_descends (prefixWord ++ tailWord_352010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352012 : List Nat := [2, 2, 1, 2, 2, 1, 3, 6]
def baseStart_352012 : Nat := 118140960795 + 352012 * 2 ^ 59
def prefixEnd_352012 : Nat := 4983230072969 + 3 ^ 40 * 352012 * 2
def baseEnd_352012 : Nat := 107111912385530065262893

theorem tailTrace_352012 : CollatzResearch.WordTrace tailWord_352012 prefixEnd_352012 107111912385530065262893 := by
  unfold tailWord_352012
  simp only [CollatzResearch.WordTrace]
  refine ⟨6419466200364058854201145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8559288267152078472268193 6419466200364058854201145)
  ·
    refine ⟨4814599650273044140650859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6419466200364058854201145 4814599650273044140650859)
    ·
      refine ⟨7221899475409566210976289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4814599650273044140650859 7221899475409566210976289)
      ·
        refine ⟨5416424606557174658232217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7221899475409566210976289 5416424606557174658232217)
        ·
          refine ⟨4062318454917880993674163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5416424606557174658232217 4062318454917880993674163)
          ·
            refine ⟨6093477682376821490511245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062318454917880993674163 6093477682376821490511245)
            ·
              refine ⟨2285054130891308058941717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6093477682376821490511245 2285054130891308058941717)
              ·
                refine ⟨107111912385530065262893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2285054130891308058941717 107111912385530065262893)
                ·
                  rfl

theorem cell19_352012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_352012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352012 prefixEnd_352012 := by exact prefixLift 352012
  have htrace : WordTrace (prefixWord ++ tailWord_352012) baseStart_352012 baseEnd_352012 := by
    simpa [prefixWord, tailWord_352012, baseEnd_352012] using wordTrace_append hprefix tailTrace_352012
  have hstable : (prefixWord ++ tailWord_352012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352012).length < 2 ^ (prefixWord ++ tailWord_352012).sum := by decide
  have hdescent : baseEnd_352012 < baseStart_352012 := by decide
  rcases family_descends (prefixWord ++ tailWord_352012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352031 : List Nat := [1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_352031 : Nat := 118140960795 + 352031 * 2 ^ 59
def prefixEnd_352031 : Nat := 4983230072969 + 3 ^ 40 * 352031 * 2
def baseEnd_352031 : Nat := 107117693797343650840619

theorem tailTrace_352031 : CollatzResearch.WordTrace tailWord_352031 prefixEnd_352031 107117693797343650840619 := by
  unfold tailWord_352031
  simp only [CollatzResearch.WordTrace]
  refine ⟨12839625387659283953343947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8559750258439522635562631 12839625387659283953343947)
  ·
    refine ⟨19259438081488925930015921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12839625387659283953343947 19259438081488925930015921)
    ·
      refine ⟨14444578561116694447511941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19259438081488925930015921 14444578561116694447511941)
      ·
        refine ⟨2708358480209380208908489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14444578561116694447511941 2708358480209380208908489)
        ·
          refine ⟨2031268860157035156681367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2708358480209380208908489 2031268860157035156681367)
          ·
            refine ⟨3046903290235552735022051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2031268860157035156681367 3046903290235552735022051)
            ·
              refine ⟨4570354935353329102533077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3046903290235552735022051 4570354935353329102533077)
              ·
                refine ⟨107117693797343650840619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4570354935353329102533077 107117693797343650840619)
                ·
                  rfl

theorem cell19_352031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_352031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352031 prefixEnd_352031 := by exact prefixLift 352031
  have htrace : WordTrace (prefixWord ++ tailWord_352031) baseStart_352031 baseEnd_352031 := by
    simpa [prefixWord, tailWord_352031, baseEnd_352031] using wordTrace_append hprefix tailTrace_352031
  have hstable : (prefixWord ++ tailWord_352031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352031).length < 2 ^ (prefixWord ++ tailWord_352031).sum := by decide
  have hdescent : baseEnd_352031 < baseStart_352031 := by decide
  rcases family_descends (prefixWord ++ tailWord_352031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352046 : List Nat := [4, 1, 3, 2, 3, 6]
def baseStart_352046 : Nat := 118140960795 + 352046 * 2 ^ 59
def prefixEnd_352046 : Nat := 4983230072969 + 3 ^ 40 * 352046 * 2
def baseEnd_352046 : Nat := 11902473118869784500805

theorem tailTrace_352046 : CollatzResearch.WordTrace tailWord_352046 prefixEnd_352046 11902473118869784500805 := by
  unfold tailWord_352046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605021560325617689392499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8560114988403294343426661 1605021560325617689392499)
  ·
    refine ⟨2407532340488426534088749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1605021560325617689392499 2407532340488426534088749)
    ·
      refine ⟨902824627683159950283281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2407532340488426534088749 902824627683159950283281)
      ·
        refine ⟨677118470762369962712461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 902824627683159950283281 677118470762369962712461)
        ·
          refine ⟨253919426535888736017173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 677118470762369962712461 253919426535888736017173)
          ·
            refine ⟨11902473118869784500805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 253919426535888736017173 11902473118869784500805)
            ·
              rfl

theorem cell19_352046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 6].length) (baseStart_352046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352046 prefixEnd_352046 := by exact prefixLift 352046
  have htrace : WordTrace (prefixWord ++ tailWord_352046) baseStart_352046 baseEnd_352046 := by
    simpa [prefixWord, tailWord_352046, baseEnd_352046] using wordTrace_append hprefix tailTrace_352046
  have hstable : (prefixWord ++ tailWord_352046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352046).length < 2 ^ (prefixWord ++ tailWord_352046).sum := by decide
  have hdescent : baseEnd_352046 < baseStart_352046 := by decide
  rcases family_descends (prefixWord ++ tailWord_352046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352050 : List Nat := [3, 2, 1, 1, 3, 9]
def baseStart_352050 : Nat := 118140960795 + 352050 * 2 ^ 59
def prefixEnd_352050 : Nat := 4983230072969 + 3 ^ 40 * 352050 * 2
def baseEnd_352050 : Nat := 11902608356573026268705

theorem tailTrace_352050 : CollatzResearch.WordTrace tailWord_352050 prefixEnd_352050 11902608356573026268705 := by
  unfold tailWord_352050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210079593647612549571401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8560212249726966798857069 3210079593647612549571401)
  ·
    refine ⟨2407559695235709412178551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3210079593647612549571401 2407559695235709412178551)
    ·
      refine ⟨3611339542853564118267827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2407559695235709412178551 3611339542853564118267827)
      ·
        refine ⟨5417009314280346177401741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611339542853564118267827 5417009314280346177401741)
        ·
          refine ⟨2031378492855129816525653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5417009314280346177401741 2031378492855129816525653)
          ·
            refine ⟨11902608356573026268705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2031378492855129816525653 11902608356573026268705)
            ·
              rfl

theorem cell19_352050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 9].length) (baseStart_352050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352050 prefixEnd_352050 := by exact prefixLift 352050
  have htrace : WordTrace (prefixWord ++ tailWord_352050) baseStart_352050 baseEnd_352050 := by
    simpa [prefixWord, tailWord_352050, baseEnd_352050] using wordTrace_append hprefix tailTrace_352050
  have hstable : (prefixWord ++ tailWord_352050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352050).length < 2 ^ (prefixWord ++ tailWord_352050).sum := by decide
  have hdescent : baseEnd_352050 < baseStart_352050 := by decide
  rcases family_descends (prefixWord ++ tailWord_352050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352067 : List Nat := [1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_352067 : Nat := 118140960795 + 352067 * 2 ^ 59
def prefixEnd_352067 : Nat := 4983230072969 + 3 ^ 40 * 352067 * 2
def baseEnd_352067 : Nat := 107128648051306234040521

theorem tailTrace_352067 : CollatzResearch.WordTrace tailWord_352067 prefixEnd_352067 107128648051306234040521 := by
  unfold tailWord_352067
  simp only [CollatzResearch.WordTrace]
  refine ⟨12840938415528862101654455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8560625610352574734436303 12840938415528862101654455)
  ·
    refine ⟨19261407623293293152481683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12840938415528862101654455 19261407623293293152481683)
    ·
      refine ⟨28892111434939939728722525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19261407623293293152481683 28892111434939939728722525)
      ·
        refine ⟨10834541788102477398270947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28892111434939939728722525 10834541788102477398270947)
        ·
          refine ⟨16251812682153716097406421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10834541788102477398270947 16251812682153716097406421)
          ·
            refine ⟨380901859737977721032963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16251812682153716097406421 380901859737977721032963)
            ·
              refine ⟨571352789606966581549445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380901859737977721032963 571352789606966581549445)
              ·
                refine ⟨107128648051306234040521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571352789606966581549445 107128648051306234040521)
                ·
                  rfl

theorem cell19_352067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_352067 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352067 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352067 prefixEnd_352067 := by exact prefixLift 352067
  have htrace : WordTrace (prefixWord ++ tailWord_352067) baseStart_352067 baseEnd_352067 := by
    simpa [prefixWord, tailWord_352067, baseEnd_352067] using wordTrace_append hprefix tailTrace_352067
  have hstable : (prefixWord ++ tailWord_352067).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352067).length < 2 ^ (prefixWord ++ tailWord_352067).sum := by decide
  have hdescent : baseEnd_352067 < baseStart_352067 := by decide
  rcases family_descends (prefixWord ++ tailWord_352067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352084 : List Nat := [2, 4, 1, 1, 3, 2, 3, 3]
def baseStart_352084 : Nat := 118140960795 + 352084 * 2 ^ 59
def prefixEnd_352084 : Nat := 4983230072969 + 3 ^ 40 * 352084 * 2
def baseEnd_352084 : Nat := 107133820893455231662697

theorem tailTrace_352084 : CollatzResearch.WordTrace tailWord_352084 prefixEnd_352084 107133820893455231662697 := by
  unfold tailWord_352084
  simp only [CollatzResearch.WordTrace]
  refine ⟨6420779228233637002511653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8561038970978182670015537 6420779228233637002511653)
  ·
    refine ⟨1203896105293806937970935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6420779228233637002511653 1203896105293806937970935)
    ·
      refine ⟨1805844157940710406956403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203896105293806937970935 1805844157940710406956403)
      ·
        refine ⟨2708766236911065610434605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805844157940710406956403 2708766236911065610434605)
        ·
          refine ⟨1015787338841649603912977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2708766236911065610434605 1015787338841649603912977)
          ·
            refine ⟨761840504131237202934733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1015787338841649603912977 761840504131237202934733)
            ·
              refine ⟨285690189049213951100525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 761840504131237202934733 285690189049213951100525)
              ·
                refine ⟨107133820893455231662697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285690189049213951100525 107133820893455231662697)
                ·
                  rfl

theorem cell19_352084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_352084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352084 prefixEnd_352084 := by exact prefixLift 352084
  have htrace : WordTrace (prefixWord ++ tailWord_352084) baseStart_352084 baseEnd_352084 := by
    simpa [prefixWord, tailWord_352084, baseEnd_352084] using wordTrace_append hprefix tailTrace_352084
  have hstable : (prefixWord ++ tailWord_352084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352084).length < 2 ^ (prefixWord ++ tailWord_352084).sum := by decide
  have hdescent : baseEnd_352084 < baseStart_352084 := by decide
  rcases family_descends (prefixWord ++ tailWord_352084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352158 : List Nat := [4, 3, 1, 3, 1, 2, 5]
def baseStart_352158 : Nat := 118140960795 + 352158 * 2 ^ 59
def prefixEnd_352158 : Nat := 4983230072969 + 3 ^ 40 * 352158 * 2
def baseEnd_352158 : Nat := 35718779323681662006017

theorem tailTrace_352158 : CollatzResearch.WordTrace tailWord_352158 prefixEnd_352158 35718779323681662006017 := by
  unfold tailWord_352158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605532182274898080402141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8562838305466123095478085 1605532182274898080402141)
  ·
    refine ⟨602074568353086780150803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1605532182274898080402141 602074568353086780150803)
    ·
      refine ⟨903111852529630170226205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 602074568353086780150803 903111852529630170226205)
      ·
        refine ⟨338666944698611313834827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 903111852529630170226205 338666944698611313834827)
        ·
          refine ⟨508000417047916970752241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338666944698611313834827 508000417047916970752241)
          ·
            refine ⟨381000312785937728064181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508000417047916970752241 381000312785937728064181)
            ·
              refine ⟨35718779323681662006017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 381000312785937728064181 35718779323681662006017)
              ·
                rfl

theorem cell19_352158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_352158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352158 prefixEnd_352158 := by exact prefixLift 352158
  have htrace : WordTrace (prefixWord ++ tailWord_352158) baseStart_352158 baseEnd_352158 := by
    simpa [prefixWord, tailWord_352158, baseEnd_352158] using wordTrace_append hprefix tailTrace_352158
  have hstable : (prefixWord ++ tailWord_352158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352158).length < 2 ^ (prefixWord ++ tailWord_352158).sum := by decide
  have hdescent : baseEnd_352158 < baseStart_352158 := by decide
  rcases family_descends (prefixWord ++ tailWord_352158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352164 : List Nat := [2, 3, 1, 2, 1, 3, 7]
def baseStart_352164 : Nat := 118140960795 + 352164 * 2 ^ 59
def prefixEnd_352164 : Nat := 4983230072969 + 3 ^ 40 * 352164 * 2
def baseEnd_352164 : Nat := 35719387893346249961567

theorem tailTrace_352164 : CollatzResearch.WordTrace tailWord_352164 prefixEnd_352164 35719387893346249961567 := by
  unfold tailWord_352164
  simp only [CollatzResearch.WordTrace]
  refine ⟨6422238148088723833967773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8562984197451631778623697 6422238148088723833967773)
  ·
    refine ⟨2408339305533271437737915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6422238148088723833967773 2408339305533271437737915)
    ·
      refine ⟨3612508958299907156606873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2408339305533271437737915 3612508958299907156606873)
      ·
        refine ⟨2709381718724930367455155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3612508958299907156606873 2709381718724930367455155)
        ·
          refine ⟨4064072578087395551182733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2709381718724930367455155 4064072578087395551182733)
          ·
            refine ⟨1524027216782773331693525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4064072578087395551182733 1524027216782773331693525)
            ·
              refine ⟨35719387893346249961567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1524027216782773331693525 35719387893346249961567)
              ·
                rfl

theorem cell19_352164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_352164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352164 prefixEnd_352164 := by exact prefixLift 352164
  have htrace : WordTrace (prefixWord ++ tailWord_352164) baseStart_352164 baseEnd_352164 := by
    simpa [prefixWord, tailWord_352164, baseEnd_352164] using wordTrace_append hprefix tailTrace_352164
  have hstable : (prefixWord ++ tailWord_352164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352164).length < 2 ^ (prefixWord ++ tailWord_352164).sum := by decide
  have hdescent : baseEnd_352164 < baseStart_352164 := by decide
  rcases family_descends (prefixWord ++ tailWord_352164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352181 : List Nat := [1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_352181 : Nat := 118140960795 + 352181 * 2 ^ 59
def prefixEnd_352181 : Nat := 4983230072969 + 3 ^ 40 * 352181 * 2
def baseEnd_352181 : Nat := 107163336522187747506877

theorem tailTrace_352181 : CollatzResearch.WordTrace tailWord_352181 prefixEnd_352181 107163336522187747506877 := by
  unfold tailWord_352181
  simp only [CollatzResearch.WordTrace]
  refine ⟨12845096337115859571304397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8563397558077239714202931 12845096337115859571304397)
  ·
    refine ⟨4816911126418447339239149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12845096337115859571304397 4816911126418447339239149)
    ·
      refine ⟨1806341672406917752214681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4816911126418447339239149 1806341672406917752214681)
      ·
        refine ⟨1354756254305188314161011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1806341672406917752214681 1354756254305188314161011)
        ·
          refine ⟨2032134381457782471241517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1354756254305188314161011 2032134381457782471241517)
          ·
            refine ⟨762050393046668426715569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2032134381457782471241517 762050393046668426715569)
            ·
              refine ⟨571537794785001320036677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762050393046668426715569 571537794785001320036677)
              ·
                refine ⟨107163336522187747506877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571537794785001320036677 107163336522187747506877)
                ·
                  rfl

theorem cell19_352181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_352181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352181 prefixEnd_352181 := by exact prefixLift 352181
  have htrace : WordTrace (prefixWord ++ tailWord_352181) baseStart_352181 baseEnd_352181 := by
    simpa [prefixWord, tailWord_352181, baseEnd_352181] using wordTrace_append hprefix tailTrace_352181
  have hstable : (prefixWord ++ tailWord_352181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352181).length < 2 ^ (prefixWord ++ tailWord_352181).sum := by decide
  have hdescent : baseEnd_352181 < baseStart_352181 := by decide
  rcases family_descends (prefixWord ++ tailWord_352181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352202 : List Nat := [3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_352202 : Nat := 118140960795 + 352202 * 2 ^ 59
def prefixEnd_352202 : Nat := 4983230072969 + 3 ^ 40 * 352202 * 2
def baseEnd_352202 : Nat := 107169726503665921040153

theorem tailTrace_352202 : CollatzResearch.WordTrace tailWord_352202 prefixEnd_352202 107169726503665921040153 := by
  unfold tailWord_352202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3211465567509945039454715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8563908180026520105212573 3211465567509945039454715)
  ·
    refine ⟨4817198351264917559182073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3211465567509945039454715 4817198351264917559182073)
    ·
      refine ⟨3612898763448688169386555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4817198351264917559182073 3612898763448688169386555)
      ·
        refine ⟨5419348145173032254079833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3612898763448688169386555 5419348145173032254079833)
        ·
          refine ⟨4064511108879774190559875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5419348145173032254079833 4064511108879774190559875)
          ·
            refine ⟨6096766663319661285839813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4064511108879774190559875 6096766663319661285839813)
            ·
              refine ⟨1143143749372436491094965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6096766663319661285839813 1143143749372436491094965)
              ·
                refine ⟨107169726503665921040153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1143143749372436491094965 107169726503665921040153)
                ·
                  rfl

theorem cell19_352202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_352202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352202 prefixEnd_352202 := by exact prefixLift 352202
  have htrace : WordTrace (prefixWord ++ tailWord_352202) baseStart_352202 baseEnd_352202 := by
    simpa [prefixWord, tailWord_352202, baseEnd_352202] using wordTrace_append hprefix tailTrace_352202
  have hstable : (prefixWord ++ tailWord_352202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352202).length < 2 ^ (prefixWord ++ tailWord_352202).sum := by decide
  have hdescent : baseEnd_352202 < baseStart_352202 := by decide
  rcases family_descends (prefixWord ++ tailWord_352202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352221 : List Nat := [1, 4, 3, 1, 10]
def baseStart_352221 : Nat := 118140960795 + 352221 * 2 ^ 59
def prefixEnd_352221 : Nat := 4983230072969 + 3 ^ 40 * 352221 * 2
def baseEnd_352221 : Nat := 3969463256128870615477

theorem tailTrace_352221 : CollatzResearch.WordTrace tailWord_352221 prefixEnd_352221 3969463256128870615477 := by
  unfold tailWord_352221
  simp only [CollatzResearch.WordTrace]
  refine ⟨12846555256970946402760517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8564370171313964268507011 12846555256970946402760517)
  ·
    refine ⟨2408729110682052450517597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12846555256970946402760517 2408729110682052450517597)
    ·
      refine ⟨903273416505769668944099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2408729110682052450517597 903273416505769668944099)
      ·
        refine ⟨1354910124758654503416149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903273416505769668944099 1354910124758654503416149)
        ·
          refine ⟨3969463256128870615477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1354910124758654503416149 3969463256128870615477)
          ·
            rfl

theorem cell19_352221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 10].length) (baseStart_352221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352221 prefixEnd_352221 := by exact prefixLift 352221
  have htrace : WordTrace (prefixWord ++ tailWord_352221) baseStart_352221 baseEnd_352221 := by
    simpa [prefixWord, tailWord_352221, baseEnd_352221] using wordTrace_append hprefix tailTrace_352221
  have hstable : (prefixWord ++ tailWord_352221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352221).length < 2 ^ (prefixWord ++ tailWord_352221).sum := by decide
  have hdescent : baseEnd_352221 < baseStart_352221 := by decide
  rcases family_descends (prefixWord ++ tailWord_352221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352238 : List Nat := [4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_352238 : Nat := 118140960795 + 352238 * 2 ^ 59
def prefixEnd_352238 : Nat := 4983230072969 + 3 ^ 40 * 352238 * 2
def baseEnd_352238 : Nat := 107180680757628504240055

theorem tailTrace_352238 : CollatzResearch.WordTrace tailWord_352238 prefixEnd_352238 107180680757628504240055 := by
  unfold tailWord_352238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605896912238669788266171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8564783531939572204086245 1605896912238669788266171)
  ·
    refine ⟨2408845368358004682399257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1605896912238669788266171 2408845368358004682399257)
    ·
      refine ⟨1806634026268503511799443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2408845368358004682399257 1806634026268503511799443)
      ·
        refine ⟨2709951039402755267699165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806634026268503511799443 2709951039402755267699165)
        ·
          refine ⟨1016231639776033225387187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2709951039402755267699165 1016231639776033225387187)
          ·
            refine ⟨1524347459664049838080781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016231639776033225387187 1524347459664049838080781)
            ·
              refine ⟨571630297374018689280293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1524347459664049838080781 571630297374018689280293)
              ·
                refine ⟨107180680757628504240055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571630297374018689280293 107180680757628504240055)
                ·
                  rfl

theorem cell19_352238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_352238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352238 prefixEnd_352238 := by exact prefixLift 352238
  have htrace : WordTrace (prefixWord ++ tailWord_352238) baseStart_352238 baseEnd_352238 := by
    simpa [prefixWord, tailWord_352238, baseEnd_352238] using wordTrace_append hprefix tailTrace_352238
  have hstable : (prefixWord ++ tailWord_352238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352238).length < 2 ^ (prefixWord ++ tailWord_352238).sum := by decide
  have hdescent : baseEnd_352238 < baseStart_352238 := by decide
  rcases family_descends (prefixWord ++ tailWord_352238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352240 : List Nat := [2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_352240 : Nat := 118140960795 + 352240 * 2 ^ 59
def prefixEnd_352240 : Nat := 4983230072969 + 3 ^ 40 * 352240 * 2
def baseEnd_352240 : Nat := 107181289327293092195605

theorem tailTrace_352240 : CollatzResearch.WordTrace tailWord_352240 prefixEnd_352240 107181289327293092195605 := by
  unfold tailWord_352240
  simp only [CollatzResearch.WordTrace]
  refine ⟨6423624121951056323851087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8564832162601408431801449 6423624121951056323851087)
  ·
    refine ⟨9635436182926584485776631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6423624121951056323851087 9635436182926584485776631)
    ·
      refine ⟨14453154274389876728664947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9635436182926584485776631 14453154274389876728664947)
      ·
        refine ⟨21679731411584815092997421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14453154274389876728664947 21679731411584815092997421)
        ·
          refine ⟨8129899279344305659874033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21679731411584815092997421 8129899279344305659874033)
          ·
            refine ⟨6097424459508229244905525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8129899279344305659874033 6097424459508229244905525)
            ·
              refine ⟨571633543078896491709893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6097424459508229244905525 571633543078896491709893)
              ·
                refine ⟨107181289327293092195605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571633543078896491709893 107181289327293092195605)
                ·
                  rfl

theorem cell19_352240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_352240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352240 prefixEnd_352240 := by exact prefixLift 352240
  have htrace : WordTrace (prefixWord ++ tailWord_352240) baseStart_352240 baseEnd_352240 := by
    simpa [prefixWord, tailWord_352240, baseEnd_352240] using wordTrace_append hprefix tailTrace_352240
  have hstable : (prefixWord ++ tailWord_352240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352240).length < 2 ^ (prefixWord ++ tailWord_352240).sum := by decide
  have hdescent : baseEnd_352240 < baseStart_352240 := by decide
  rcases family_descends (prefixWord ++ tailWord_352240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352257 : List Nat := [1, 2, 4, 1, 2, 1, 5, 3]
def baseStart_352257 : Nat := 118140960795 + 352257 * 2 ^ 59
def prefixEnd_352257 : Nat := 4983230072969 + 3 ^ 40 * 352257 * 2
def baseEnd_352257 : Nat := 107186462169442089817781

theorem tailTrace_352257 : CollatzResearch.WordTrace tailWord_352257 prefixEnd_352257 107186462169442089817781 := by
  unfold tailWord_352257
  simp only [CollatzResearch.WordTrace]
  refine ⟨12847868284840524551071025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8565245523227016367380683 12847868284840524551071025)
  ·
    refine ⟨9635901213630393413303269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12847868284840524551071025 9635901213630393413303269)
    ·
      refine ⟨1806731477555698764994363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9635901213630393413303269 1806731477555698764994363)
      ·
        refine ⟨2710097216333548147491545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806731477555698764994363 2710097216333548147491545)
        ·
          refine ⟨2032572912250161110618659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2710097216333548147491545 2032572912250161110618659)
          ·
            refine ⟨3048859368375241665927989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032572912250161110618659 3048859368375241665927989)
            ·
              refine ⟨285830565785178906180749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3048859368375241665927989 285830565785178906180749)
              ·
                refine ⟨107186462169442089817781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285830565785178906180749 107186462169442089817781)
                ·
                  rfl

theorem cell19_352257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_352257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352257 prefixEnd_352257 := by exact prefixLift 352257
  have htrace : WordTrace (prefixWord ++ tailWord_352257) baseStart_352257 baseEnd_352257 := by
    simpa [prefixWord, tailWord_352257, baseEnd_352257] using wordTrace_append hprefix tailTrace_352257
  have hstable : (prefixWord ++ tailWord_352257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352257).length < 2 ^ (prefixWord ++ tailWord_352257).sum := by decide
  have hdescent : baseEnd_352257 < baseStart_352257 := by decide
  rcases family_descends (prefixWord ++ tailWord_352257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352308 : List Nat := [2, 5, 1, 2, 3, 1, 2, 3]
def baseStart_352308 : Nat := 118140960795 + 352308 * 2 ^ 59
def prefixEnd_352308 : Nat := 4983230072969 + 3 ^ 40 * 352308 * 2
def baseEnd_352308 : Nat := 107201980695889082684309

theorem tailTrace_352308 : CollatzResearch.WordTrace tailWord_352308 prefixEnd_352308 107201980695889082684309 := by
  unfold tailWord_352308
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424864203827880130588789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8566485605103840174118385 6424864203827880130588789)
  ·
    refine ⟨602331019108863762242699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6424864203827880130588789 602331019108863762242699)
    ·
      refine ⟨903496528663295643364049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 602331019108863762242699 903496528663295643364049)
      ·
        refine ⟨677622396497471732523037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 903496528663295643364049 677622396497471732523037)
        ·
          refine ⟨254108398686551899696139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 677622396497471732523037 254108398686551899696139)
          ·
            refine ⟨381162598029827849544209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254108398686551899696139 381162598029827849544209)
            ·
              refine ⟨285871948522370887158157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381162598029827849544209 285871948522370887158157)
              ·
                refine ⟨107201980695889082684309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285871948522370887158157 107201980695889082684309)
                ·
                  rfl

theorem cell19_352308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_352308 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352308 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352308 prefixEnd_352308 := by exact prefixLift 352308
  have htrace : WordTrace (prefixWord ++ tailWord_352308) baseStart_352308 baseEnd_352308 := by
    simpa [prefixWord, tailWord_352308, baseEnd_352308] using wordTrace_append hprefix tailTrace_352308
  have hstable : (prefixWord ++ tailWord_352308).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352308).length < 2 ^ (prefixWord ++ tailWord_352308).sum := by decide
  have hdescent : baseEnd_352308 < baseStart_352308 := by decide
  rcases family_descends (prefixWord ++ tailWord_352308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352312 : List Nat := [2, 1, 2, 1, 6, 2, 2, 3]
def baseStart_352312 : Nat := 118140960795 + 352312 * 2 ^ 59
def prefixEnd_352312 : Nat := 4983230072969 + 3 ^ 40 * 352312 * 2
def baseEnd_352312 : Nat := 107203197835218258595409

theorem tailTrace_352312 : CollatzResearch.WordTrace tailWord_352312 prefixEnd_352312 107203197835218258595409 := by
  unfold tailWord_352312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424937149820634472161595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8566582866427512629548793 6424937149820634472161595)
  ·
    refine ⟨9637405724730951708242393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6424937149820634472161595 9637405724730951708242393)
    ·
      refine ⟨7228054293548213781181795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9637405724730951708242393 7228054293548213781181795)
      ·
        refine ⟨10842081440322320671772693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7228054293548213781181795 10842081440322320671772693)
        ·
          refine ⟨508222567515108781489345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10842081440322320671772693 508222567515108781489345)
          ·
            refine ⟨381166925636331586117009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508222567515108781489345 381166925636331586117009)
            ·
              refine ⟨285875194227248689587757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381166925636331586117009 285875194227248689587757)
              ·
                refine ⟨107203197835218258595409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285875194227248689587757 107203197835218258595409)
                ·
                  rfl

theorem cell19_352312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_352312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352312 prefixEnd_352312 := by exact prefixLift 352312
  have htrace : WordTrace (prefixWord ++ tailWord_352312) baseStart_352312 baseEnd_352312 := by
    simpa [prefixWord, tailWord_352312, baseEnd_352312] using wordTrace_append hprefix tailTrace_352312
  have hstable : (prefixWord ++ tailWord_352312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352312).length < 2 ^ (prefixWord ++ tailWord_352312).sum := by decide
  have hdescent : baseEnd_352312 < baseStart_352312 := by decide
  rcases family_descends (prefixWord ++ tailWord_352312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352316 : List Nat := [2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_352316 : Nat := 118140960795 + 352316 * 2 ^ 59
def prefixEnd_352316 : Nat := 4983230072969 + 3 ^ 40 * 352316 * 2
def baseEnd_352316 : Nat := 107204414974547434506509

theorem tailTrace_352316 : CollatzResearch.WordTrace tailWord_352316 prefixEnd_352316 107204414974547434506509 := by
  unfold tailWord_352316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6425010095813388813734401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8566680127751185084979201 6425010095813388813734401)
  ·
    refine ⟨4818757571860041610300801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6425010095813388813734401 4818757571860041610300801)
    ·
      refine ⟨3614068178895031207725601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4818757571860041610300801 3614068178895031207725601)
      ·
        refine ⟨2710551134171273405794201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3614068178895031207725601 2710551134171273405794201)
        ·
          refine ⟨2032913350628455054345651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2710551134171273405794201 2032913350628455054345651)
          ·
            refine ⟨3049370025942682581518477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032913350628455054345651 3049370025942682581518477)
            ·
              refine ⟨1143513759728505968069429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3049370025942682581518477 1143513759728505968069429)
              ·
                refine ⟨107204414974547434506509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1143513759728505968069429 107204414974547434506509)
                ·
                  rfl

theorem cell19_352316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_352316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352316 prefixEnd_352316 := by exact prefixLift 352316
  have htrace : WordTrace (prefixWord ++ tailWord_352316) baseStart_352316 baseEnd_352316 := by
    simpa [prefixWord, tailWord_352316, baseEnd_352316] using wordTrace_append hprefix tailTrace_352316
  have hstable : (prefixWord ++ tailWord_352316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352316).length < 2 ^ (prefixWord ++ tailWord_352316).sum := by decide
  have hdescent : baseEnd_352316 < baseStart_352316 := by decide
  rcases family_descends (prefixWord ++ tailWord_352316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352392 : List Nat := [2, 1, 3, 4, 1, 8]
def baseStart_352392 : Nat := 118140960795 + 352392 * 2 ^ 59
def prefixEnd_352392 : Nat := 4983230072969 + 3 ^ 40 * 352392 * 2
def baseEnd_352392 : Nat := 11914171180200197424157

theorem tailTrace_352392 : CollatzResearch.WordTrace tailWord_352392 prefixEnd_352392 11914171180200197424157 := by
  unfold tailWord_352392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6426396069675721303617715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8568528092900961738156953 6426396069675721303617715)
  ·
    refine ⟨9639594104513581955426573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6426396069675721303617715 9639594104513581955426573)
    ·
      refine ⟨3614847789192593233284965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9639594104513581955426573 3614847789192593233284965)
      ·
        refine ⟨677783960473611231240931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3614847789192593233284965 677783960473611231240931)
        ·
          refine ⟨1016675940710416846861397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677783960473611231240931 1016675940710416846861397)
          ·
            refine ⟨11914171180200197424157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1016675940710416846861397 11914171180200197424157)
            ·
              rfl

theorem cell19_352392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 8].length) (baseStart_352392 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352392 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352392 prefixEnd_352392 := by exact prefixLift 352392
  have htrace : WordTrace (prefixWord ++ tailWord_352392) baseStart_352392 baseEnd_352392 := by
    simpa [prefixWord, tailWord_352392, baseEnd_352392] using wordTrace_append hprefix tailTrace_352392
  have hstable : (prefixWord ++ tailWord_352392).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352392).length < 2 ^ (prefixWord ++ tailWord_352392).sum := by decide
  have hdescent : baseEnd_352392 < baseStart_352392 := by decide
  rcases family_descends (prefixWord ++ tailWord_352392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352407 : List Nat := [1, 1, 3, 3, 5, 1, 1, 4]
def baseStart_352407 : Nat := 118140960795 + 352407 * 2 ^ 59
def prefixEnd_352407 : Nat := 4983230072969 + 3 ^ 40 * 352407 * 2
def baseEnd_352407 : Nat := 107232104894286186484039

theorem tailTrace_352407 : CollatzResearch.WordTrace tailWord_352407 prefixEnd_352407 107232104894286186484039 := by
  unfold tailWord_352407
  simp only [CollatzResearch.WordTrace]
  refine ⟨12853339234297100169031475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8568892822864733446020983 12853339234297100169031475)
  ·
    refine ⟨19280008851445650253547213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12853339234297100169031475 19280008851445650253547213)
    ·
      refine ⟨7230003319292118845080205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19280008851445650253547213 7230003319292118845080205)
      ·
        refine ⟨2711251244734544566905077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7230003319292118845080205 2711251244734544566905077)
        ·
          refine ⟨254179804193863553147351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2711251244734544566905077 254179804193863553147351)
          ·
            refine ⟨381269706290795329721027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254179804193863553147351 381269706290795329721027)
            ·
              refine ⟨571904559436192994581541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381269706290795329721027 571904559436192994581541)
              ·
                refine ⟨107232104894286186484039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571904559436192994581541 107232104894286186484039)
                ·
                  rfl

theorem cell19_352407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 4].length) (baseStart_352407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352407 prefixEnd_352407 := by exact prefixLift 352407
  have htrace : WordTrace (prefixWord ++ tailWord_352407) baseStart_352407 baseEnd_352407 := by
    simpa [prefixWord, tailWord_352407, baseEnd_352407] using wordTrace_append hprefix tailTrace_352407
  have hstable : (prefixWord ++ tailWord_352407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352407).length < 2 ^ (prefixWord ++ tailWord_352407).sum := by decide
  have hdescent : baseEnd_352407 < baseStart_352407 := by decide
  rcases family_descends (prefixWord ++ tailWord_352407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352485 : List Nat := [1, 3, 1, 4, 2, 1, 4, 3]
def baseStart_352485 : Nat := 118140960795 + 352485 * 2 ^ 59
def prefixEnd_352485 : Nat := 4983230072969 + 3 ^ 40 * 352485 * 2
def baseEnd_352485 : Nat := 107255839111205116750493

theorem tailTrace_352485 : CollatzResearch.WordTrace tailWord_352485 prefixEnd_352485 107255839111205116750493 := by
  unfold tailWord_352485
  simp only [CollatzResearch.WordTrace]
  refine ⟨12856184128014519490370909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8570789418676346326913939 12856184128014519490370909)
  ·
    refine ⟨4821069048005444808889091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12856184128014519490370909 4821069048005444808889091)
    ·
      refine ⟨7231603572008167213333637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4821069048005444808889091 7231603572008167213333637)
      ·
        refine ⟨1355925669751531352500057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7231603572008167213333637 1355925669751531352500057)
        ·
          refine ⟨1016944252313648514375043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355925669751531352500057 1016944252313648514375043)
          ·
            refine ⟨1525416378470472771562565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016944252313648514375043 1525416378470472771562565)
            ·
              refine ⟨286015570963213644667981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1525416378470472771562565 286015570963213644667981)
              ·
                refine ⟨107255839111205116750493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286015570963213644667981 107255839111205116750493)
                ·
                  rfl

theorem cell19_352485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_352485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352485 prefixEnd_352485 := by exact prefixLift 352485
  have htrace : WordTrace (prefixWord ++ tailWord_352485) baseStart_352485 baseEnd_352485 := by
    simpa [prefixWord, tailWord_352485, baseEnd_352485] using wordTrace_append hprefix tailTrace_352485
  have hstable : (prefixWord ++ tailWord_352485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352485).length < 2 ^ (prefixWord ++ tailWord_352485).sum := by decide
  have hdescent : baseEnd_352485 < baseStart_352485 := by decide
  rcases family_descends (prefixWord ++ tailWord_352485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352489 : List Nat := [1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_352489 : Nat := 118140960795 + 352489 * 2 ^ 59
def prefixEnd_352489 : Nat := 4983230072969 + 3 ^ 40 * 352489 * 2
def baseEnd_352489 : Nat := 107257056250534292661593

theorem tailTrace_352489 : CollatzResearch.WordTrace tailWord_352489 prefixEnd_352489 107257056250534292661593 := by
  unfold tailWord_352489
  simp only [CollatzResearch.WordTrace]
  refine ⟨12856330020000028173516521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8570886680000018782344347 12856330020000028173516521)
  ·
    refine ⟨9642247515000021130137391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12856330020000028173516521 9642247515000021130137391)
    ·
      refine ⟨14463371272500031695206087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9642247515000021130137391 14463371272500031695206087)
      ·
        refine ⟨21695056908750047542809131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14463371272500031695206087 21695056908750047542809131)
        ·
          refine ⟨32542585363125071314213697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21695056908750047542809131 32542585363125071314213697)
          ·
            refine ⟨24406939022343803485660273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32542585363125071314213697 24406939022343803485660273)
            ·
              refine ⟨18305204266757852614245205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24406939022343803485660273 18305204266757852614245205)
              ·
                refine ⟨107257056250534292661593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18305204266757852614245205 107257056250534292661593)
                ·
                  rfl

theorem cell19_352489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_352489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352489 prefixEnd_352489 := by exact prefixLift 352489
  have htrace : WordTrace (prefixWord ++ tailWord_352489) baseStart_352489 baseEnd_352489 := by
    simpa [prefixWord, tailWord_352489, baseEnd_352489] using wordTrace_append hprefix tailTrace_352489
  have hstable : (prefixWord ++ tailWord_352489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352489).length < 2 ^ (prefixWord ++ tailWord_352489).sum := by decide
  have hdescent : baseEnd_352489 < baseStart_352489 := by decide
  rcases family_descends (prefixWord ++ tailWord_352489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352506 : List Nat := [3, 1, 1, 1, 1, 7, 5]
def baseStart_352506 : Nat := 118140960795 + 352506 * 2 ^ 59
def prefixEnd_352506 : Nat := 4983230072969 + 3 ^ 40 * 352506 * 2
def baseEnd_352506 : Nat := 35754076364227763427923

theorem tailTrace_352506 : CollatzResearch.WordTrace tailWord_352506 prefixEnd_352506 35754076364227763427923 := by
  unfold tailWord_352506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214237515234610019221343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8571300040625626717923581 3214237515234610019221343)
  ·
    refine ⟨4821356272851915028832015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3214237515234610019221343 4821356272851915028832015)
    ·
      refine ⟨7232034409277872543248023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4821356272851915028832015 7232034409277872543248023)
      ·
        refine ⟨10848051613916808814872035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7232034409277872543248023 10848051613916808814872035)
        ·
          refine ⟨16272077420875213222308053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10848051613916808814872035 16272077420875213222308053)
          ·
            refine ⟨381376814551762809897845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16272077420875213222308053 381376814551762809897845)
            ·
              refine ⟨35754076364227763427923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 381376814551762809897845 35754076364227763427923)
              ·
                rfl

theorem cell19_352506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_352506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352506 prefixEnd_352506 := by exact prefixLift 352506
  have htrace : WordTrace (prefixWord ++ tailWord_352506) baseStart_352506 baseEnd_352506 := by
    simpa [prefixWord, tailWord_352506, baseEnd_352506] using wordTrace_append hprefix tailTrace_352506
  have hstable : (prefixWord ++ tailWord_352506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352506).length < 2 ^ (prefixWord ++ tailWord_352506).sum := by decide
  have hdescent : baseEnd_352506 < baseStart_352506 := by decide
  rcases family_descends (prefixWord ++ tailWord_352506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352544 : List Nat := [2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_352544 : Nat := 118140960795 + 352544 * 2 ^ 59
def prefixEnd_352544 : Nat := 4983230072969 + 3 ^ 40 * 352544 * 2
def baseEnd_352544 : Nat := 107273791916310461439221

theorem tailTrace_352544 : CollatzResearch.WordTrace tailWord_352544 prefixEnd_352544 107273791916310461439221 := by
  unfold tailWord_352544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6429168017400386283384343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8572224023200515044512457 6429168017400386283384343)
  ·
    refine ⟨9643752026100579425076515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6429168017400386283384343 9643752026100579425076515)
    ·
      refine ⟨14465628039150869137614773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9643752026100579425076515 14465628039150869137614773)
      ·
        refine ⟨1356152628670393981651385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14465628039150869137614773 1356152628670393981651385)
        ·
          refine ⟨1017114471502795486238539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1356152628670393981651385 1017114471502795486238539)
          ·
            refine ⟨1525671707254193229357809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017114471502795486238539 1525671707254193229357809)
            ·
              refine ⟨1144253780440644922018357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1525671707254193229357809 1144253780440644922018357)
              ·
                refine ⟨107273791916310461439221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1144253780440644922018357 107273791916310461439221)
                ·
                  rfl

theorem cell19_352544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_352544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352544 prefixEnd_352544 := by exact prefixLift 352544
  have htrace : WordTrace (prefixWord ++ tailWord_352544) baseStart_352544 baseEnd_352544 := by
    simpa [prefixWord, tailWord_352544, baseEnd_352544] using wordTrace_append hprefix tailTrace_352544
  have hstable : (prefixWord ++ tailWord_352544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352544).length < 2 ^ (prefixWord ++ tailWord_352544).sum := by decide
  have hdescent : baseEnd_352544 < baseStart_352544 := by decide
  rcases family_descends (prefixWord ++ tailWord_352544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352620 : List Nat := [2, 2, 1, 1, 6, 1, 6]
def baseStart_352620 : Nat := 118140960795 + 352620 * 2 ^ 59
def prefixEnd_352620 : Nat := 4983230072969 + 3 ^ 40 * 352620 * 2
def baseEnd_352620 : Nat := 35765639187854934583375

theorem tailTrace_352620 : CollatzResearch.WordTrace tailWord_352620 prefixEnd_352620 35765639187854934583375 := by
  unfold tailWord_352620
  simp only [CollatzResearch.WordTrace]
  refine ⟨6430553991262718773267657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8574071988350291697690209 6430553991262718773267657)
  ·
    refine ⟨4822915493447039079950743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6430553991262718773267657 4822915493447039079950743)
    ·
      refine ⟨7234373240170558619926115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4822915493447039079950743 7234373240170558619926115)
      ·
        refine ⟨10851559860255837929889173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7234373240170558619926115 10851559860255837929889173)
        ·
          refine ⟨508666868449492402963555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10851559860255837929889173 508666868449492402963555)
          ·
            refine ⟨763000302674238604445333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508666868449492402963555 763000302674238604445333)
            ·
              refine ⟨35765639187854934583375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 763000302674238604445333 35765639187854934583375)
              ·
                rfl

theorem cell19_352620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_352620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352620 prefixEnd_352620 := by exact prefixLift 352620
  have htrace : WordTrace (prefixWord ++ tailWord_352620) baseStart_352620 baseEnd_352620 := by
    simpa [prefixWord, tailWord_352620, baseEnd_352620] using wordTrace_append hprefix tailTrace_352620
  have hstable : (prefixWord ++ tailWord_352620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352620).length < 2 ^ (prefixWord ++ tailWord_352620).sum := by decide
  have hdescent : baseEnd_352620 < baseStart_352620 := by decide
  rcases family_descends (prefixWord ++ tailWord_352620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352654 : List Nat := [4, 1, 1, 4, 1, 3, 2, 3]
def baseStart_352654 : Nat := 118140960795 + 352654 * 2 ^ 59
def prefixEnd_352654 : Nat := 4983230072969 + 3 ^ 40 * 352654 * 2
def baseEnd_352654 : Nat := 107307263247862798994477

theorem tailTrace_352654 : CollatzResearch.WordTrace tailWord_352654 prefixEnd_352654 107307263247862798994477 := by
  unfold tailWord_352654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1607793508050282669159127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8574898709601507568848677 1607793508050282669159127)
  ·
    refine ⟨2411690262075424003738691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1607793508050282669159127 2411690262075424003738691)
    ·
      refine ⟨3617535393113136005608037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2411690262075424003738691 3617535393113136005608037)
      ·
        refine ⟨678287886208713001051507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3617535393113136005608037 678287886208713001051507)
        ·
          refine ⟨1017431829313069501577261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678287886208713001051507 1017431829313069501577261)
          ·
            refine ⟨381536935992401063091473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1017431829313069501577261 381536935992401063091473)
            ·
              refine ⟨286152701994300797318605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381536935992401063091473 286152701994300797318605)
              ·
                refine ⟨107307263247862798994477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286152701994300797318605 107307263247862798994477)
                ·
                  rfl

theorem cell19_352654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_352654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352654 prefixEnd_352654 := by exact prefixLift 352654
  have htrace : WordTrace (prefixWord ++ tailWord_352654) baseStart_352654 baseEnd_352654 := by
    simpa [prefixWord, tailWord_352654, baseEnd_352654] using wordTrace_append hprefix tailTrace_352654
  have hstable : (prefixWord ++ tailWord_352654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352654).length < 2 ^ (prefixWord ++ tailWord_352654).sum := by decide
  have hdescent : baseEnd_352654 < baseStart_352654 := by decide
  rcases family_descends (prefixWord ++ tailWord_352654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352673 : List Nat := [1, 2, 3, 5, 2, 1, 5]
def baseStart_352673 : Nat := 118140960795 + 352673 * 2 ^ 59
def prefixEnd_352673 : Nat := 4983230072969 + 3 ^ 40 * 352673 * 2
def baseEnd_352673 : Nat := 35771014886558794857401

theorem tailTrace_352673 : CollatzResearch.WordTrace tailWord_352673 prefixEnd_352673 35771014886558794857401 := by
  unfold tailWord_352673
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863041051333427598214673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8575360700888951732143115 12863041051333427598214673)
  ·
    refine ⟨9647280788500070698661005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12863041051333427598214673 9647280788500070698661005)
    ·
      refine ⟨3617730295687526511997877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9647280788500070698661005 3617730295687526511997877)
      ·
        refine ⟨339162215220705610499801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3617730295687526511997877 339162215220705610499801)
        ·
          refine ⟨254371661415529207874851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339162215220705610499801 254371661415529207874851)
          ·
            refine ⟨381557492123293811812277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254371661415529207874851 381557492123293811812277)
            ·
              refine ⟨35771014886558794857401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 381557492123293811812277 35771014886558794857401)
              ·
                rfl

theorem cell19_352673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 5].length) (baseStart_352673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352673 prefixEnd_352673 := by exact prefixLift 352673
  have htrace : WordTrace (prefixWord ++ tailWord_352673) baseStart_352673 baseEnd_352673 := by
    simpa [prefixWord, tailWord_352673, baseEnd_352673] using wordTrace_append hprefix tailTrace_352673
  have hstable : (prefixWord ++ tailWord_352673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352673).length < 2 ^ (prefixWord ++ tailWord_352673).sum := by decide
  have hdescent : baseEnd_352673 < baseStart_352673 := by decide
  rcases family_descends (prefixWord ++ tailWord_352673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352829 : List Nat := [1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_352829 : Nat := 118140960795 + 352829 * 2 ^ 59
def prefixEnd_352829 : Nat := 4983230072969 + 3 ^ 40 * 352829 * 2
def baseEnd_352829 : Nat := 107360513093514245105111

theorem tailTrace_352829 : CollatzResearch.WordTrace tailWord_352829 prefixEnd_352829 107360513093514245105111 := by
  unfold tailWord_352829
  simp only [CollatzResearch.WordTrace]
  refine ⟨12868730838768266240893541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8579153892512177493929027 12868730838768266240893541)
  ·
    refine ⟨2412887032269049920167539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12868730838768266240893541 2412887032269049920167539)
    ·
      refine ⟨3619330548403574880251309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412887032269049920167539 3619330548403574880251309)
      ·
        refine ⟨1357248955651340580094241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3619330548403574880251309 1357248955651340580094241)
        ·
          refine ⟨1017936716738505435070681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1357248955651340580094241 1017936716738505435070681)
          ·
            refine ⟨763452537553879076303011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1017936716738505435070681 763452537553879076303011)
            ·
              refine ⟨1145178806330818614454517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763452537553879076303011 1145178806330818614454517)
              ·
                refine ⟨107360513093514245105111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1145178806330818614454517 107360513093514245105111)
                ·
                  rfl

theorem cell19_352829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_352829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352829 prefixEnd_352829 := by exact prefixLift 352829
  have htrace : WordTrace (prefixWord ++ tailWord_352829) baseStart_352829 baseEnd_352829 := by
    simpa [prefixWord, tailWord_352829, baseEnd_352829] using wordTrace_append hprefix tailTrace_352829
  have hstable : (prefixWord ++ tailWord_352829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352829).length < 2 ^ (prefixWord ++ tailWord_352829).sum := by decide
  have hdescent : baseEnd_352829 < baseStart_352829 := by decide
  rcases family_descends (prefixWord ++ tailWord_352829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352831 : List Nat := [1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_352831 : Nat := 118140960795 + 352831 * 2 ^ 59
def prefixEnd_352831 : Nat := 4983230072969 + 3 ^ 40 * 352831 * 2
def baseEnd_352831 : Nat := 107361121663178833060661

theorem tailTrace_352831 : CollatzResearch.WordTrace tailWord_352831 prefixEnd_352831 107361121663178833060661 := by
  unfold tailWord_352831
  simp only [CollatzResearch.WordTrace]
  refine ⟨12868803784761020582466347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8579202523174013721644231 12868803784761020582466347)
  ·
    refine ⟨19303205677141530873699521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12868803784761020582466347 19303205677141530873699521)
    ·
      refine ⟨14477404257856148155274641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19303205677141530873699521 14477404257856148155274641)
      ·
        refine ⟨10858053193392111116455981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14477404257856148155274641 10858053193392111116455981)
        ·
          refine ⟨4071769947522041668670993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10858053193392111116455981 4071769947522041668670993)
          ·
            refine ⟨3053827460641531251503245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4071769947522041668670993 3053827460641531251503245)
            ·
              refine ⟨1145185297740574219313717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053827460641531251503245 1145185297740574219313717)
              ·
                refine ⟨107361121663178833060661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1145185297740574219313717 107361121663178833060661)
                ·
                  rfl

theorem cell19_352831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_352831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352831 prefixEnd_352831 := by exact prefixLift 352831
  have htrace : WordTrace (prefixWord ++ tailWord_352831) baseStart_352831 baseEnd_352831 := by
    simpa [prefixWord, tailWord_352831, baseEnd_352831] using wordTrace_append hprefix tailTrace_352831
  have hstable : (prefixWord ++ tailWord_352831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352831).length < 2 ^ (prefixWord ++ tailWord_352831).sum := by decide
  have hdescent : baseEnd_352831 < baseStart_352831 := by decide
  rcases family_descends (prefixWord ++ tailWord_352831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352924 : List Nat := [2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_352924 : Nat := 118140960795 + 352924 * 2 ^ 59
def prefixEnd_352924 : Nat := 4983230072969 + 3 ^ 40 * 352924 * 2
def baseEnd_352924 : Nat := 107389420152582172993741

theorem tailTrace_352924 : CollatzResearch.WordTrace tailWord_352924 prefixEnd_352924 107389420152582172993741 := by
  unfold tailWord_352924
  simp only [CollatzResearch.WordTrace]
  refine ⟨6436097886712048732800913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8581463848949398310401217 6436097886712048732800913)
  ·
    refine ⟨4827073415034036549600685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6436097886712048732800913 4827073415034036549600685)
    ·
      refine ⟨1810152530637763706100257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4827073415034036549600685 1810152530637763706100257)
      ·
        refine ⟨1357614397978322779575193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1810152530637763706100257 1357614397978322779575193)
        ·
          refine ⟨1018210798483742084681395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1357614397978322779575193 1018210798483742084681395)
          ·
            refine ⟨1527316197725613127022093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018210798483742084681395 1527316197725613127022093)
            ·
              refine ⟨572743574147104922633285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527316197725613127022093 572743574147104922633285)
              ·
                refine ⟨107389420152582172993741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 572743574147104922633285 107389420152582172993741)
                ·
                  rfl

theorem cell19_352924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_352924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352924 prefixEnd_352924 := by exact prefixLift 352924
  have htrace : WordTrace (prefixWord ++ tailWord_352924) baseStart_352924 baseEnd_352924 := by
    simpa [prefixWord, tailWord_352924, baseEnd_352924] using wordTrace_append hprefix tailTrace_352924
  have hstable : (prefixWord ++ tailWord_352924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352924).length < 2 ^ (prefixWord ++ tailWord_352924).sum := by decide
  have hdescent : baseEnd_352924 < baseStart_352924 := by decide
  rcases family_descends (prefixWord ++ tailWord_352924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352941 : List Nat := [1, 5, 2, 1, 1, 3, 3, 3]
def baseStart_352941 : Nat := 118140960795 + 352941 * 2 ^ 59
def prefixEnd_352941 : Nat := 4983230072969 + 3 ^ 40 * 352941 * 2
def baseEnd_352941 : Nat := 107394592994731170615917

theorem tailTrace_352941 : CollatzResearch.WordTrace tailWord_352941 prefixEnd_352941 107394592994731170615917 := by
  unfold tailWord_352941
  simp only [CollatzResearch.WordTrace]
  refine ⟨12872815814362509368970677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8581877209575006245980451 12872815814362509368970677)
  ·
    refine ⟨1206826482596485253341001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12872815814362509368970677 1206826482596485253341001)
    ·
      refine ⟨905119861947363940005751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1206826482596485253341001 905119861947363940005751)
      ·
        refine ⟨1357679792921045910008627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905119861947363940005751 1357679792921045910008627)
        ·
          refine ⟨2036519689381568865012941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357679792921045910008627 2036519689381568865012941)
          ·
            refine ⟨763694883518088324379853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2036519689381568865012941 763694883518088324379853)
            ·
              refine ⟨286385581319283121642445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 763694883518088324379853 286385581319283121642445)
              ·
                refine ⟨107394592994731170615917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286385581319283121642445 107394592994731170615917)
                ·
                  rfl

theorem cell19_352941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_352941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352941 prefixEnd_352941 := by exact prefixLift 352941
  have htrace : WordTrace (prefixWord ++ tailWord_352941) baseStart_352941 baseEnd_352941 := by
    simpa [prefixWord, tailWord_352941, baseEnd_352941] using wordTrace_append hprefix tailTrace_352941
  have hstable : (prefixWord ++ tailWord_352941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352941).length < 2 ^ (prefixWord ++ tailWord_352941).sum := by decide
  have hdescent : baseEnd_352941 < baseStart_352941 := by decide
  rcases family_descends (prefixWord ++ tailWord_352941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352943 : List Nat := [1, 1, 2, 1, 2, 6, 3, 3]
def baseStart_352943 : Nat := 118140960795 + 352943 * 2 ^ 59
def prefixEnd_352943 : Nat := 4983230072969 + 3 ^ 40 * 352943 * 2
def baseEnd_352943 : Nat := 107395201564395758571467

theorem tailTrace_352943 : CollatzResearch.WordTrace tailWord_352943 prefixEnd_352943 107395201564395758571467 := by
  unfold tailWord_352943
  simp only [CollatzResearch.WordTrace]
  refine ⟨12872888760355263710543483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8581925840236842473695655 12872888760355263710543483)
  ·
    refine ⟨19309333140532895565815225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12872888760355263710543483 19309333140532895565815225)
    ·
      refine ⟨14481999855399671674361419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19309333140532895565815225 14481999855399671674361419)
      ·
        refine ⟨21722999783099507511542129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14481999855399671674361419 21722999783099507511542129)
        ·
          refine ⟨16292249837324630633656597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21722999783099507511542129 16292249837324630633656597)
          ·
            refine ⟨763699211124592060952653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16292249837324630633656597 763699211124592060952653)
            ·
              refine ⟨286387204171722022857245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 763699211124592060952653 286387204171722022857245)
              ·
                refine ⟨107395201564395758571467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286387204171722022857245 107395201564395758571467)
                ·
                  rfl

theorem cell19_352943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_352943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_352943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_352943 prefixEnd_352943 := by exact prefixLift 352943
  have htrace : WordTrace (prefixWord ++ tailWord_352943) baseStart_352943 baseEnd_352943 := by
    simpa [prefixWord, tailWord_352943, baseEnd_352943] using wordTrace_append hprefix tailTrace_352943
  have hstable : (prefixWord ++ tailWord_352943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352943).length < 2 ^ (prefixWord ++ tailWord_352943).sum := by decide
  have hdescent : baseEnd_352943 < baseStart_352943 := by decide
  rcases family_descends (prefixWord ++ tailWord_352943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353000 : List Nat := [2, 1, 4, 1, 4, 1, 1, 5]
def baseStart_353000 : Nat := 118140960795 + 353000 * 2 ^ 59
def prefixEnd_353000 : Nat := 4983230072969 + 3 ^ 40 * 353000 * 2
def baseEnd_353000 : Nat := 107412545799836515304645

theorem tailTrace_353000 : CollatzResearch.WordTrace tailWord_353000 prefixEnd_353000 107412545799836515304645 := by
  unfold tailWord_353000
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437483860574381222684227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8583311814099174963578969 6437483860574381222684227)
  ·
    refine ⟨9656225790861571834026341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6437483860574381222684227 9656225790861571834026341)
    ·
      refine ⟨1810542335786544718879939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9656225790861571834026341 1810542335786544718879939)
      ·
        refine ⟨2715813503679817078319909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810542335786544718879939 2715813503679817078319909)
        ·
          refine ⟨509215031939965702184983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2715813503679817078319909 509215031939965702184983)
          ·
            refine ⟨763822547909948553277475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509215031939965702184983 763822547909948553277475)
            ·
              refine ⟨1145733821864922829916213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763822547909948553277475 1145733821864922829916213)
              ·
                refine ⟨107412545799836515304645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1145733821864922829916213 107412545799836515304645)
                ·
                  rfl

theorem cell19_353000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_353000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353000 prefixEnd_353000 := by exact prefixLift 353000
  have htrace : WordTrace (prefixWord ++ tailWord_353000) baseStart_353000 baseEnd_353000 := by
    simpa [prefixWord, tailWord_353000, baseEnd_353000] using wordTrace_append hprefix tailTrace_353000
  have hstable : (prefixWord ++ tailWord_353000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353000).length < 2 ^ (prefixWord ++ tailWord_353000).sum := by decide
  have hdescent : baseEnd_353000 < baseStart_353000 := by decide
  rcases family_descends (prefixWord ++ tailWord_353000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353013 : List Nat := [1, 3, 6, 1, 2, 1, 5]
def baseStart_353013 : Nat := 118140960795 + 353013 * 2 ^ 59
def prefixEnd_353013 : Nat := 4983230072969 + 3 ^ 40 * 353013 * 2
def baseEnd_353013 : Nat := 35805500500885445671907

theorem tailTrace_353013 : CollatzResearch.WordTrace tailWord_353013 prefixEnd_353013 35805500500885445671907 := by
  unfold tailWord_353013
  simp only [CollatzResearch.WordTrace]
  refine ⟨12875441870101665665591693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8583627913401110443727795 12875441870101665665591693)
  ·
    refine ⟨4828290701288124624596885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12875441870101665665591693 4828290701288124624596885)
    ·
      refine ⟨226326126622880841777979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4828290701288124624596885 226326126622880841777979)
      ·
        refine ⟨339489189934321262666969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226326126622880841777979 339489189934321262666969)
        ·
          refine ⟨254616892450740947000227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339489189934321262666969 254616892450740947000227)
          ·
            refine ⟨381925338676111420500341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254616892450740947000227 381925338676111420500341)
            ·
              refine ⟨35805500500885445671907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 381925338676111420500341 35805500500885445671907)
              ·
                rfl

theorem cell19_353013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 5].length) (baseStart_353013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353013 prefixEnd_353013 := by exact prefixLift 353013
  have htrace : WordTrace (prefixWord ++ tailWord_353013) baseStart_353013 baseEnd_353013 := by
    simpa [prefixWord, tailWord_353013, baseEnd_353013] using wordTrace_append hprefix tailTrace_353013
  have hstable : (prefixWord ++ tailWord_353013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353013).length < 2 ^ (prefixWord ++ tailWord_353013).sum := by decide
  have hdescent : baseEnd_353013 < baseStart_353013 := by decide
  rcases family_descends (prefixWord ++ tailWord_353013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353076 : List Nat := [2, 5, 1, 1, 3, 7]
def baseStart_353076 : Nat := 118140960795 + 353076 * 2 ^ 59
def prefixEnd_353076 : Nat := 4983230072969 + 3 ^ 40 * 353076 * 2
def baseEnd_353076 : Nat := 11937296827454539735061

theorem tailTrace_353076 : CollatzResearch.WordTrace tailWord_353076 prefixEnd_353076 11937296827454539735061 := by
  unfold tailWord_353076
  simp only [CollatzResearch.WordTrace]
  refine ⟨6438869834436713712567541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8585159779248951616756721 6438869834436713712567541)
  ·
    refine ⟨603644046978441910553207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6438869834436713712567541 603644046978441910553207)
    ·
      refine ⟨905466070467662865829811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603644046978441910553207 905466070467662865829811)
      ·
        refine ⟨1358199105701494298744717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905466070467662865829811 1358199105701494298744717)
        ·
          refine ⟨509324664638060362029269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1358199105701494298744717 509324664638060362029269)
          ·
            refine ⟨11937296827454539735061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 509324664638060362029269 11937296827454539735061)
            ·
              rfl

theorem cell19_353076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 7].length) (baseStart_353076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353076 prefixEnd_353076 := by exact prefixLift 353076
  have htrace : WordTrace (prefixWord ++ tailWord_353076) baseStart_353076 baseEnd_353076 := by
    simpa [prefixWord, tailWord_353076, baseEnd_353076] using wordTrace_append hprefix tailTrace_353076
  have hstable : (prefixWord ++ tailWord_353076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353076).length < 2 ^ (prefixWord ++ tailWord_353076).sum := by decide
  have hdescent : baseEnd_353076 < baseStart_353076 := by decide
  rcases family_descends (prefixWord ++ tailWord_353076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353097 : List Nat := [1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_353097 : Nat := 118140960795 + 353097 * 2 ^ 59
def prefixEnd_353097 : Nat := 4983230072969 + 3 ^ 40 * 353097 * 2
def baseEnd_353097 : Nat := 107442061428569031148825

theorem tailTrace_353097 : CollatzResearch.WordTrace tailWord_353097 prefixEnd_353097 107442061428569031148825 := by
  unfold tailWord_353097
  simp only [CollatzResearch.WordTrace]
  refine ⟨12878505601797348011649545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8585670401198232007766363 12878505601797348011649545)
  ·
    refine ⟨9658879201348011008737159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12878505601797348011649545 9658879201348011008737159)
    ·
      refine ⟨14488318802022016513105739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9658879201348011008737159 14488318802022016513105739)
      ·
        refine ⟨21732478203033024769658609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14488318802022016513105739 21732478203033024769658609)
        ·
          refine ⟨16299358652274768577243957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21732478203033024769658609 16299358652274768577243957)
          ·
            refine ⟨1528064873650759554116621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16299358652274768577243957 1528064873650759554116621)
            ·
              refine ⟨573024327619034832793733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1528064873650759554116621 573024327619034832793733)
              ·
                refine ⟨107442061428569031148825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 573024327619034832793733 107442061428569031148825)
                ·
                  rfl

theorem cell19_353097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_353097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353097 prefixEnd_353097 := by exact prefixLift 353097
  have htrace : WordTrace (prefixWord ++ tailWord_353097) baseStart_353097 baseEnd_353097 := by
    simpa [prefixWord, tailWord_353097, baseEnd_353097] using wordTrace_append hprefix tailTrace_353097
  have hstable : (prefixWord ++ tailWord_353097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353097).length < 2 ^ (prefixWord ++ tailWord_353097).sum := by decide
  have hdescent : baseEnd_353097 < baseStart_353097 := by decide
  rcases family_descends (prefixWord ++ tailWord_353097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353114 : List Nat := [3, 1, 1, 2, 1, 5, 3, 3]
def baseStart_353114 : Nat := 118140960795 + 353114 * 2 ^ 59
def prefixEnd_353114 : Nat := 4983230072969 + 3 ^ 40 * 353114 * 2
def baseEnd_353114 : Nat := 107447234270718028771001

theorem tailTrace_353114 : CollatzResearch.WordTrace tailWord_353114 prefixEnd_353114 107447234270718028771001 := by
  unfold tailWord_353114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219781410683939978754599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8586083761823839943345597 3219781410683939978754599)
  ·
    refine ⟨4829672116025909968131899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3219781410683939978754599 4829672116025909968131899)
    ·
      refine ⟨7244508174038864952197849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4829672116025909968131899 7244508174038864952197849)
      ·
        refine ⟨5433381130529148714148387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7244508174038864952197849 5433381130529148714148387)
        ·
          refine ⟨8150071695793723071222581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433381130529148714148387 8150071695793723071222581)
          ·
            refine ⟨764069221480661537927117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8150071695793723071222581 764069221480661537927117)
            ·
              refine ⟨286525958055248076722669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 764069221480661537927117 286525958055248076722669)
              ·
                refine ⟨107447234270718028771001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286525958055248076722669 107447234270718028771001)
                ·
                  rfl

theorem cell19_353114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_353114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353114 prefixEnd_353114 := by exact prefixLift 353114
  have htrace : WordTrace (prefixWord ++ tailWord_353114) baseStart_353114 baseEnd_353114 := by
    simpa [prefixWord, tailWord_353114, baseEnd_353114] using wordTrace_append hprefix tailTrace_353114
  have hstable : (prefixWord ++ tailWord_353114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353114).length < 2 ^ (prefixWord ++ tailWord_353114).sum := by decide
  have hdescent : baseEnd_353114 < baseStart_353114 := by decide
  rcases family_descends (prefixWord ++ tailWord_353114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353173 : List Nat := [1, 3, 2, 1, 1, 5, 1, 5]
def baseStart_353173 : Nat := 118140960795 + 353173 * 2 ^ 59
def prefixEnd_353173 : Nat := 4983230072969 + 3 ^ 40 * 353173 * 2
def baseEnd_353173 : Nat := 107465187075823373459729

theorem tailTrace_353173 : CollatzResearch.WordTrace tailWord_353173 prefixEnd_353173 107465187075823373459729 := by
  unfold tailWord_353173
  simp only [CollatzResearch.WordTrace]
  refine ⟨12881277549522012991416173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8587518366348008660944115 12881277549522012991416173)
  ·
    refine ⟨4830479081070754871781065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12881277549522012991416173 4830479081070754871781065)
    ·
      refine ⟨3622859310803066153835799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4830479081070754871781065 3622859310803066153835799)
      ·
        refine ⟨5434288966204599230753699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622859310803066153835799 5434288966204599230753699)
        ·
          refine ⟨8151433449306898846130549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5434288966204599230753699 8151433449306898846130549)
          ·
            refine ⟨764196885872521766824739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8151433449306898846130549 764196885872521766824739)
            ·
              refine ⟨1146295328808782650237109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764196885872521766824739 1146295328808782650237109)
              ·
                refine ⟨107465187075823373459729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1146295328808782650237109 107465187075823373459729)
                ·
                  rfl

theorem cell19_353173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_353173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353173 prefixEnd_353173 := by exact prefixLift 353173
  have htrace : WordTrace (prefixWord ++ tailWord_353173) baseStart_353173 baseEnd_353173 := by
    simpa [prefixWord, tailWord_353173, baseEnd_353173] using wordTrace_append hprefix tailTrace_353173
  have hstable : (prefixWord ++ tailWord_353173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353173).length < 2 ^ (prefixWord ++ tailWord_353173).sum := by decide
  have hdescent : baseEnd_353173 < baseStart_353173 := by decide
  rcases family_descends (prefixWord ++ tailWord_353173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353230 : List Nat := [4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_353230 : Nat := 118140960795 + 353230 * 2 ^ 59
def prefixEnd_353230 : Nat := 4983230072969 + 3 ^ 40 * 353230 * 2
def baseEnd_353230 : Nat := 107482531311264130192907

theorem tailTrace_353230 : CollatzResearch.WordTrace tailWord_353230 prefixEnd_353230 107482531311264130192907 := by
  unfold tailWord_353230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1610419563789438965780143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8588904340210341150827429 1610419563789438965780143)
  ·
    refine ⟨2415629345684158448670215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1610419563789438965780143 2415629345684158448670215)
    ·
      refine ⟨3623444018526237673005323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415629345684158448670215 3623444018526237673005323)
      ·
        refine ⟨5435166027789356509507985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3623444018526237673005323 5435166027789356509507985)
        ·
          refine ⟨4076374520842017382130989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5435166027789356509507985 4076374520842017382130989)
          ·
            refine ⟨1528640445315756518299121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4076374520842017382130989 1528640445315756518299121)
            ·
              refine ⟨1146480333986817388724341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528640445315756518299121 1146480333986817388724341)
              ·
                refine ⟨107482531311264130192907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1146480333986817388724341 107482531311264130192907)
                ·
                  rfl

theorem cell19_353230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_353230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353230 prefixEnd_353230 := by exact prefixLift 353230
  have htrace : WordTrace (prefixWord ++ tailWord_353230) baseStart_353230 baseEnd_353230 := by
    simpa [prefixWord, tailWord_353230, baseEnd_353230] using wordTrace_append hprefix tailTrace_353230
  have hstable : (prefixWord ++ tailWord_353230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353230).length < 2 ^ (prefixWord ++ tailWord_353230).sum := by decide
  have hdescent : baseEnd_353230 < baseStart_353230 := by decide
  rcases family_descends (prefixWord ++ tailWord_353230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353289 : List Nat := [1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_353289 : Nat := 118140960795 + 353289 * 2 ^ 59
def prefixEnd_353289 : Nat := 4983230072969 + 3 ^ 40 * 353289 * 2
def baseEnd_353289 : Nat := 107500484116369474881635

theorem tailTrace_353289 : CollatzResearch.WordTrace tailWord_353289 prefixEnd_353289 107500484116369474881635 := by
  unfold tailWord_353289
  simp only [CollatzResearch.WordTrace]
  refine ⟨12885508417101764802638921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8590338944734509868425947 12885508417101764802638921)
  ·
    refine ⟨9664131312826323601979191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12885508417101764802638921 9664131312826323601979191)
    ·
      refine ⟨14496196969239485402968787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9664131312826323601979191 14496196969239485402968787)
      ·
        refine ⟨21744295453859228104453181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14496196969239485402968787 21744295453859228104453181)
        ·
          refine ⟨8154110795197210539169943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21744295453859228104453181 8154110795197210539169943)
          ·
            refine ⟨12231166192795815808754915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8154110795197210539169943 12231166192795815808754915)
            ·
              refine ⟨18346749289193723713132373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12231166192795815808754915 18346749289193723713132373)
              ·
                refine ⟨107500484116369474881635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18346749289193723713132373 107500484116369474881635)
                ·
                  rfl

theorem cell19_353289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_353289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353289 prefixEnd_353289 := by exact prefixLift 353289
  have htrace : WordTrace (prefixWord ++ tailWord_353289) baseStart_353289 baseEnd_353289 := by
    simpa [prefixWord, tailWord_353289, baseEnd_353289] using wordTrace_append hprefix tailTrace_353289
  have hstable : (prefixWord ++ tailWord_353289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353289).length < 2 ^ (prefixWord ++ tailWord_353289).sum := by decide
  have hdescent : baseEnd_353289 < baseStart_353289 := by decide
  rcases family_descends (prefixWord ++ tailWord_353289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353342 : List Nat := [4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_353342 : Nat := 118140960795 + 353342 * 2 ^ 59
def prefixEnd_353342 : Nat := 4983230072969 + 3 ^ 40 * 353342 * 2
def baseEnd_353342 : Nat := 107516611212481055703713

theorem tailTrace_353342 : CollatzResearch.WordTrace tailWord_353342 prefixEnd_353342 107516611212481055703713 := by
  unfold tailWord_353342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1610930185738719356789785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8591627657273169902878853 1610930185738719356789785)
  ·
    refine ⟨1208197639304039517592339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1610930185738719356789785 1208197639304039517592339)
    ·
      refine ⟨1812296458956059276388509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1208197639304039517592339 1812296458956059276388509)
      ·
        refine ⟨679611172108522228645691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1812296458956059276388509 679611172108522228645691)
        ·
          refine ⟨1019416758162783342968537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679611172108522228645691 1019416758162783342968537)
          ·
            refine ⟨764562568622087507226403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1019416758162783342968537 764562568622087507226403)
            ·
              refine ⟨1146843852933131260839605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764562568622087507226403 1146843852933131260839605)
              ·
                refine ⟨107516611212481055703713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1146843852933131260839605 107516611212481055703713)
                ·
                  rfl

theorem cell19_353342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_353342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353342 prefixEnd_353342 := by exact prefixLift 353342
  have htrace : WordTrace (prefixWord ++ tailWord_353342) baseStart_353342 baseEnd_353342 := by
    simpa [prefixWord, tailWord_353342, baseEnd_353342] using wordTrace_append hprefix tailTrace_353342
  have hstable : (prefixWord ++ tailWord_353342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353342).length < 2 ^ (prefixWord ++ tailWord_353342).sum := by decide
  have hdescent : baseEnd_353342 < baseStart_353342 := by decide
  rcases family_descends (prefixWord ++ tailWord_353342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353498 : List Nat := [3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_353498 : Nat := 118140960795 + 353498 * 2 ^ 59
def prefixEnd_353498 : Nat := 4983230072969 + 3 ^ 40 * 353498 * 2
def baseEnd_353498 : Nat := 107564079646318916236621

theorem tailTrace_353498 : CollatzResearch.WordTrace tailWord_353498 prefixEnd_353498 107564079646318916236621 := by
  unfold tailWord_353498
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223282818336148374249287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8595420848896395664664765 3223282818336148374249287)
  ·
    refine ⟨4834924227504222561373931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3223282818336148374249287 4834924227504222561373931)
    ·
      refine ⟨7252386341256333842060897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4834924227504222561373931 7252386341256333842060897)
      ·
        refine ⟨5439289755942250381545673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7252386341256333842060897 5439289755942250381545673)
        ·
          refine ⟨4079467316956687786159255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5439289755942250381545673 4079467316956687786159255)
          ·
            refine ⟨6119200975435031679238883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079467316956687786159255 6119200975435031679238883)
            ·
              refine ⟨9178801463152547518858325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6119200975435031679238883 9178801463152547518858325)
              ·
                refine ⟨107564079646318916236621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9178801463152547518858325 107564079646318916236621)
                ·
                  rfl

theorem cell19_353498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_353498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353498 prefixEnd_353498 := by exact prefixLift 353498
  have htrace : WordTrace (prefixWord ++ tailWord_353498) baseStart_353498 baseEnd_353498 := by
    simpa [prefixWord, tailWord_353498, baseEnd_353498] using wordTrace_append hprefix tailTrace_353498
  have hstable : (prefixWord ++ tailWord_353498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353498).length < 2 ^ (prefixWord ++ tailWord_353498).sum := by decide
  have hdescent : baseEnd_353498 < baseStart_353498 := by decide
  rcases family_descends (prefixWord ++ tailWord_353498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353511 : List Nat := [1, 1, 5, 3, 2, 2, 2, 3]
def baseStart_353511 : Nat := 118140960795 + 353511 * 2 ^ 59
def prefixEnd_353511 : Nat := 4983230072969 + 3 ^ 40 * 353511 * 2
def baseEnd_353511 : Nat := 107568035349138737947697

theorem tailTrace_353511 : CollatzResearch.WordTrace tailWord_353511 prefixEnd_353511 107568035349138737947697 := by
  unfold tailWord_353511
  simp only [CollatzResearch.WordTrace]
  refine ⟨12893605422297496717220387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8595736948198331144813591 12893605422297496717220387)
  ·
    refine ⟨19340408133446245075830581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12893605422297496717220387 19340408133446245075830581)
    ·
      refine ⟨1813163262510585475859117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19340408133446245075830581 1813163262510585475859117)
      ·
        refine ⟨679936223441469553447169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1813163262510585475859117 679936223441469553447169)
        ·
          refine ⟨509952167581102165085377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 679936223441469553447169 509952167581102165085377)
          ·
            refine ⟨382464125685826623814033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509952167581102165085377 382464125685826623814033)
            ·
              refine ⟨286848094264369967860525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382464125685826623814033 286848094264369967860525)
              ·
                refine ⟨107568035349138737947697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286848094264369967860525 107568035349138737947697)
                ·
                  rfl

theorem cell19_353511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_353511 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353511 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353511 prefixEnd_353511 := by exact prefixLift 353511
  have htrace : WordTrace (prefixWord ++ tailWord_353511) baseStart_353511 baseEnd_353511 := by
    simpa [prefixWord, tailWord_353511, baseEnd_353511] using wordTrace_append hprefix tailTrace_353511
  have hstable : (prefixWord ++ tailWord_353511).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353511).length < 2 ^ (prefixWord ++ tailWord_353511).sum := by decide
  have hdescent : baseEnd_353511 < baseStart_353511 := by decide
  rcases family_descends (prefixWord ++ tailWord_353511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353515 : List Nat := [1, 1, 1, 1, 2, 6, 4, 3]
def baseStart_353515 : Nat := 118140960795 + 353515 * 2 ^ 59
def prefixEnd_353515 : Nat := 4983230072969 + 3 ^ 40 * 353515 * 2
def baseEnd_353515 : Nat := 107569252488467913858797

theorem tailTrace_353515 : CollatzResearch.WordTrace tailWord_353515 prefixEnd_353515 107569252488467913858797 := by
  unfold tailWord_353515
  simp only [CollatzResearch.WordTrace]
  refine ⟨12893751314283005400365999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8595834209522003600243999 12893751314283005400365999)
  ·
    refine ⟨19340626971424508100548999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12893751314283005400365999 19340626971424508100548999)
    ·
      refine ⟨29010940457136762150823499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19340626971424508100548999 29010940457136762150823499)
      ·
        refine ⟨43516410685705143226235249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29010940457136762150823499 43516410685705143226235249)
        ·
          refine ⟨32637308014278857419676437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43516410685705143226235249 32637308014278857419676437)
          ·
            refine ⟨1529873813169321441547333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32637308014278857419676437 1529873813169321441547333)
            ·
              refine ⟨286851339969247770290125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1529873813169321441547333 286851339969247770290125)
              ·
                refine ⟨107569252488467913858797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286851339969247770290125 107569252488467913858797)
                ·
                  rfl

theorem cell19_353515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_353515 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353515 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353515 prefixEnd_353515 := by exact prefixLift 353515
  have htrace : WordTrace (prefixWord ++ tailWord_353515) baseStart_353515 baseEnd_353515 := by
    simpa [prefixWord, tailWord_353515, baseEnd_353515] using wordTrace_append hprefix tailTrace_353515
  have hstable : (prefixWord ++ tailWord_353515).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353515).length < 2 ^ (prefixWord ++ tailWord_353515).sum := by decide
  have hdescent : baseEnd_353515 < baseStart_353515 := by decide
  rcases family_descends (prefixWord ++ tailWord_353515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353532 : List Nat := [2, 2, 2, 1, 6, 1, 5]
def baseStart_353532 : Nat := 118140960795 + 353532 * 2 ^ 59
def prefixEnd_353532 : Nat := 4983230072969 + 3 ^ 40 * 353532 * 2
def baseEnd_353532 : Nat := 35858141776872303826991

theorem tailTrace_353532 : CollatzResearch.WordTrace tailWord_353532 prefixEnd_353532 35858141776872303826991 := by
  unfold tailWord_353532
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447185677610708651867425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8596247570147611535823233 6447185677610708651867425)
  ·
    refine ⟨4835389258208031488900569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6447185677610708651867425 4835389258208031488900569)
    ·
      refine ⟨3626541943656023616675427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4835389258208031488900569 3626541943656023616675427)
      ·
        refine ⟨5439812915484035425013141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626541943656023616675427 5439812915484035425013141)
        ·
          refine ⟨254991230413314160547491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5439812915484035425013141 254991230413314160547491)
          ·
            refine ⟨382486845619971240821237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254991230413314160547491 382486845619971240821237)
            ·
              refine ⟨35858141776872303826991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 382486845619971240821237 35858141776872303826991)
              ·
                rfl

theorem cell19_353532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 5].length) (baseStart_353532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353532 prefixEnd_353532 := by exact prefixLift 353532
  have htrace : WordTrace (prefixWord ++ tailWord_353532) baseStart_353532 baseEnd_353532 := by
    simpa [prefixWord, tailWord_353532, baseEnd_353532] using wordTrace_append hprefix tailTrace_353532
  have hstable : (prefixWord ++ tailWord_353532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353532).length < 2 ^ (prefixWord ++ tailWord_353532).sum := by decide
  have hdescent : baseEnd_353532 < baseStart_353532 := by decide
  rcases family_descends (prefixWord ++ tailWord_353532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353534 : List Nat := [4, 2, 2, 1, 1, 2, 7]
def baseStart_353534 : Nat := 118140960795 + 353534 * 2 ^ 59
def prefixEnd_353534 : Nat := 4983230072969 + 3 ^ 40 * 353534 * 2
def baseEnd_353534 : Nat := 35858344633427166478841

theorem tailTrace_353534 : CollatzResearch.WordTrace tailWord_353534 prefixEnd_353534 35858344633427166478841 := by
  unfold tailWord_353534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1611805537651771455663457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8596296200809447763538437 1611805537651771455663457)
  ·
    refine ⟨1208854153238828591747593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1611805537651771455663457 1208854153238828591747593)
    ·
      refine ⟨906640614929121443810695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1208854153238828591747593 906640614929121443810695)
      ·
        refine ⟨1359960922393682165716043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906640614929121443810695 1359960922393682165716043)
        ·
          refine ⟨2039941383590523248574065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359960922393682165716043 2039941383590523248574065)
          ·
            refine ⟨1529956037692892436430549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2039941383590523248574065 1529956037692892436430549)
            ·
              refine ⟨35858344633427166478841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1529956037692892436430549 35858344633427166478841)
              ·
                rfl

theorem cell19_353534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_353534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353534 prefixEnd_353534 := by exact prefixLift 353534
  have htrace : WordTrace (prefixWord ++ tailWord_353534) baseStart_353534 baseEnd_353534 := by
    simpa [prefixWord, tailWord_353534, baseEnd_353534] using wordTrace_append hprefix tailTrace_353534
  have hstable : (prefixWord ++ tailWord_353534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353534).length < 2 ^ (prefixWord ++ tailWord_353534).sum := by decide
  have hdescent : baseEnd_353534 < baseStart_353534 := by decide
  rcases family_descends (prefixWord ++ tailWord_353534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353593 : List Nat := [1, 2, 1, 6, 9]
def baseStart_353593 : Nat := 118140960795 + 353593 * 2 ^ 59
def prefixEnd_353593 : Nat := 4983230072969 + 3 ^ 40 * 353593 * 2
def baseEnd_353593 : Nat := 3984925433532846078713

theorem tailTrace_353593 : CollatzResearch.WordTrace tailWord_353593 prefixEnd_353593 3984925433532846078713 := by
  unfold tailWord_353593
  simp only [CollatzResearch.WordTrace]
  refine ⟨12896596208000424721705433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8597730805333616481136955 12896596208000424721705433)
  ·
    refine ⟨9672447156000318541279075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12896596208000424721705433 9672447156000318541279075)
    ·
      refine ⟨14508670734000477811918613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9672447156000318541279075 14508670734000477811918613)
      ·
        refine ⟨680093940656272397433685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14508670734000477811918613 680093940656272397433685)
        ·
          refine ⟨3984925433532846078713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 680093940656272397433685 3984925433532846078713)
          ·
            rfl

theorem cell19_353593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 9].length) (baseStart_353593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353593 prefixEnd_353593 := by exact prefixLift 353593
  have htrace : WordTrace (prefixWord ++ tailWord_353593) baseStart_353593 baseEnd_353593 := by
    simpa [prefixWord, tailWord_353593, baseEnd_353593] using wordTrace_append hprefix tailTrace_353593
  have hstable : (prefixWord ++ tailWord_353593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353593).length < 2 ^ (prefixWord ++ tailWord_353593).sum := by decide
  have hdescent : baseEnd_353593 < baseStart_353593 := by decide
  rcases family_descends (prefixWord ++ tailWord_353593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353646 : List Nat := [4, 1, 2, 4, 1, 1, 6]
def baseStart_353646 : Nat := 118140960795 + 353646 * 2 ^ 59
def prefixEnd_353646 : Nat := 4983230072969 + 3 ^ 40 * 353646 * 2
def baseEnd_353646 : Nat := 35869704600499474982443

theorem tailTrace_353646 : CollatzResearch.WordTrace tailWord_353646 prefixEnd_353646 35869704600499474982443 := by
  unfold tailWord_353646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612316159601051846673099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8599019517872276515589861 1612316159601051846673099)
  ·
    refine ⟨2418474239401577770009649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1612316159601051846673099 2418474239401577770009649)
    ·
      refine ⟨1813855679551183327507237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2418474239401577770009649 1813855679551183327507237)
      ·
        refine ⟨340097939915846873907607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1813855679551183327507237 340097939915846873907607)
        ·
          refine ⟨510146909873770310861411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340097939915846873907607 510146909873770310861411)
          ·
            refine ⟨765220364810655466292117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510146909873770310861411 765220364810655466292117)
            ·
              refine ⟨35869704600499474982443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 765220364810655466292117 35869704600499474982443)
              ·
                rfl

theorem cell19_353646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_353646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353646 prefixEnd_353646 := by exact prefixLift 353646
  have htrace : WordTrace (prefixWord ++ tailWord_353646) baseStart_353646 baseEnd_353646 := by
    simpa [prefixWord, tailWord_353646, baseEnd_353646] using wordTrace_append hprefix tailTrace_353646
  have hstable : (prefixWord ++ tailWord_353646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353646).length < 2 ^ (prefixWord ++ tailWord_353646).sum := by decide
  have hdescent : baseEnd_353646 < baseStart_353646 := by decide
  rcases family_descends (prefixWord ++ tailWord_353646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353650 : List Nat := [3, 2, 1, 2, 1, 2, 8]
def baseStart_353650 : Nat := 118140960795 + 353650 * 2 ^ 59
def prefixEnd_353650 : Nat := 4983230072969 + 3 ^ 40 * 353650 * 2
def baseEnd_353650 : Nat := 35870110313609200286143

theorem tailTrace_353650 : CollatzResearch.WordTrace tailWord_353650 prefixEnd_353650 35870110313609200286143 := by
  unfold tailWord_353650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3224668792198480864132601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8599116779195948971020269 3224668792198480864132601)
  ·
    refine ⟨2418501594148860648099451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3224668792198480864132601 2418501594148860648099451)
    ·
      refine ⟨3627752391223290972149177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2418501594148860648099451 3627752391223290972149177)
      ·
        refine ⟨2720814293417468229111883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3627752391223290972149177 2720814293417468229111883)
        ·
          refine ⟨4081221440126202343667825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2720814293417468229111883 4081221440126202343667825)
          ·
            refine ⟨3060916080094651757750869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4081221440126202343667825 3060916080094651757750869)
            ·
              refine ⟨35870110313609200286143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3060916080094651757750869 35870110313609200286143)
              ·
                rfl

theorem cell19_353650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_353650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353650 prefixEnd_353650 := by exact prefixLift 353650
  have htrace : WordTrace (prefixWord ++ tailWord_353650) baseStart_353650 baseEnd_353650 := by
    simpa [prefixWord, tailWord_353650, baseEnd_353650] using wordTrace_append hprefix tailTrace_353650
  have hstable : (prefixWord ++ tailWord_353650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353650).length < 2 ^ (prefixWord ++ tailWord_353650).sum := by decide
  have hdescent : baseEnd_353650 < baseStart_353650 := by decide
  rcases family_descends (prefixWord ++ tailWord_353650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353684 : List Nat := [2, 4, 2, 1, 2, 1, 4, 3]
def baseStart_353684 : Nat := 118140960795 + 353684 * 2 ^ 59
def prefixEnd_353684 : Nat := 4983230072969 + 3 ^ 40 * 353684 * 2
def baseEnd_353684 : Nat := 107620676625125596102781

theorem tailTrace_353684 : CollatzResearch.WordTrace tailWord_353684 prefixEnd_353684 107620676625125596102781 := by
  unfold tailWord_353684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6449957625335373631634053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8599943500447164842178737 6449957625335373631634053)
  ·
    refine ⟨1209367054750382555931385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6449957625335373631634053 1209367054750382555931385)
    ·
      refine ⟨907025291062786916948539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1209367054750382555931385 907025291062786916948539)
      ·
        refine ⟨1360537936594180375422809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907025291062786916948539 1360537936594180375422809)
        ·
          refine ⟨1020403452445635281567107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1360537936594180375422809 1020403452445635281567107)
          ·
            refine ⟨1530605178668452922350661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020403452445635281567107 1530605178668452922350661)
            ·
              refine ⟨286988471000334922940749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1530605178668452922350661 286988471000334922940749)
              ·
                refine ⟨107620676625125596102781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286988471000334922940749 107620676625125596102781)
                ·
                  rfl

theorem cell19_353684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_353684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353684 prefixEnd_353684 := by exact prefixLift 353684
  have htrace : WordTrace (prefixWord ++ tailWord_353684) baseStart_353684 baseEnd_353684 := by
    simpa [prefixWord, tailWord_353684, baseEnd_353684] using wordTrace_append hprefix tailTrace_353684
  have hstable : (prefixWord ++ tailWord_353684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353684).length < 2 ^ (prefixWord ++ tailWord_353684).sum := by decide
  have hdescent : baseEnd_353684 < baseStart_353684 := by decide
  rcases family_descends (prefixWord ++ tailWord_353684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353821 : List Nat := [1, 4, 2, 2, 1, 1, 8]
def baseStart_353821 : Nat := 118140960795 + 353821 * 2 ^ 59
def prefixEnd_353821 : Nat := 4983230072969 + 3 ^ 40 * 353821 * 2
def baseEnd_353821 : Nat := 35887454549049957019321

theorem tailTrace_353821 : CollatzResearch.WordTrace tailWord_353821 prefixEnd_353821 35887454549049957019321 := by
  unfold tailWord_353821
  simp only [CollatzResearch.WordTrace]
  refine ⟨12904912051174419661005317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8603274700782946440670211 12904912051174419661005317)
  ·
    refine ⟨2419671009595203686438497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12904912051174419661005317 2419671009595203686438497)
    ·
      refine ⟨1814753257196402764828873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2419671009595203686438497 1814753257196402764828873)
      ·
        refine ⟨1361064942897302073621655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1814753257196402764828873 1361064942897302073621655)
        ·
          refine ⟨2041597414345953110432483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361064942897302073621655 2041597414345953110432483)
          ·
            refine ⟨3062396121518929665648725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041597414345953110432483 3062396121518929665648725)
            ·
              refine ⟨35887454549049957019321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3062396121518929665648725 35887454549049957019321)
              ·
                rfl

theorem cell19_353821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_353821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353821 prefixEnd_353821 := by exact prefixLift 353821
  have htrace : WordTrace (prefixWord ++ tailWord_353821) baseStart_353821 baseEnd_353821 := by
    simpa [prefixWord, tailWord_353821, baseEnd_353821] using wordTrace_append hprefix tailTrace_353821
  have hstable : (prefixWord ++ tailWord_353821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353821).length < 2 ^ (prefixWord ++ tailWord_353821).sum := by decide
  have hdescent : baseEnd_353821 < baseStart_353821 := by decide
  rcases family_descends (prefixWord ++ tailWord_353821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353853 : List Nat := [1, 4, 1, 3, 4, 1, 2, 3]
def baseStart_353853 : Nat := 118140960795 + 353853 * 2 ^ 59
def prefixEnd_353853 : Nat := 4983230072969 + 3 ^ 40 * 353853 * 2
def baseEnd_353853 : Nat := 107672100761783278346765

theorem tailTrace_353853 : CollatzResearch.WordTrace tailWord_353853 prefixEnd_353853 107672100761783278346765 := by
  unfold tailWord_353853
  simp only [CollatzResearch.WordTrace]
  refine ⟨12906079187058489126170213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8604052791372326084113475 12906079187058489126170213)
  ·
    refine ⟨2419889847573466711156915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12906079187058489126170213 2419889847573466711156915)
    ·
      refine ⟨3629834771360200066735373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419889847573466711156915 3629834771360200066735373)
      ·
        refine ⟨1361188039260075025025765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3629834771360200066735373 1361188039260075025025765)
        ·
          refine ⟨255222757361264067192331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1361188039260075025025765 255222757361264067192331)
          ·
            refine ⟨382834136041896100788497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255222757361264067192331 382834136041896100788497)
            ·
              refine ⟨287125602031422075591373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382834136041896100788497 287125602031422075591373)
              ·
                refine ⟨107672100761783278346765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287125602031422075591373 107672100761783278346765)
                ·
                  rfl

theorem cell19_353853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 3].length) (baseStart_353853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353853 prefixEnd_353853 := by exact prefixLift 353853
  have htrace : WordTrace (prefixWord ++ tailWord_353853) baseStart_353853 baseEnd_353853 := by
    simpa [prefixWord, tailWord_353853, baseEnd_353853] using wordTrace_append hprefix tailTrace_353853
  have hstable : (prefixWord ++ tailWord_353853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353853).length < 2 ^ (prefixWord ++ tailWord_353853).sum := by decide
  have hdescent : baseEnd_353853 < baseStart_353853 := by decide
  rcases family_descends (prefixWord ++ tailWord_353853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353950 : List Nat := [4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_353950 : Nat := 118140960795 + 353950 * 2 ^ 59
def prefixEnd_353950 : Nat := 4983230072969 + 3 ^ 40 * 353950 * 2
def baseEnd_353950 : Nat := 107701616390515794190945

theorem tailTrace_353950 : CollatzResearch.WordTrace tailWord_353950 prefixEnd_353950 107701616390515794190945 := by
  unfold tailWord_353950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613702133463384336556413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8606411378471383128300869 1613702133463384336556413)
  ·
    refine ⟨605138300048769126208655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1613702133463384336556413 605138300048769126208655)
    ·
      refine ⟨907707450073153689312983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605138300048769126208655 907707450073153689312983)
      ·
        refine ⟨1361561175109730533969475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907707450073153689312983 1361561175109730533969475)
        ·
          refine ⟨2042341762664595800954213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361561175109730533969475 2042341762664595800954213)
          ·
            refine ⟨382939080499611712678915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2042341762664595800954213 382939080499611712678915)
            ·
              refine ⟨574408620749417569018373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382939080499611712678915 574408620749417569018373)
              ·
                refine ⟨107701616390515794190945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 574408620749417569018373 107701616390515794190945)
                ·
                  rfl

theorem cell19_353950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_353950 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353950 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353950 prefixEnd_353950 := by exact prefixLift 353950
  have htrace : WordTrace (prefixWord ++ tailWord_353950) baseStart_353950 baseEnd_353950 := by
    simpa [prefixWord, tailWord_353950, baseEnd_353950] using wordTrace_append hprefix tailTrace_353950
  have hstable : (prefixWord ++ tailWord_353950).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353950).length < 2 ^ (prefixWord ++ tailWord_353950).sum := by decide
  have hdescent : baseEnd_353950 < baseStart_353950 := by decide
  rcases family_descends (prefixWord ++ tailWord_353950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353952 : List Nat := [2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_353952 : Nat := 118140960795 + 353952 * 2 ^ 59
def prefixEnd_353952 : Nat := 4983230072969 + 3 ^ 40 * 353952 * 2
def baseEnd_353952 : Nat := 107702224960180382146495

theorem tailTrace_353952 : CollatzResearch.WordTrace tailWord_353952 prefixEnd_353952 107702224960180382146495 := by
  unfold tailWord_353952
  simp only [CollatzResearch.WordTrace]
  refine ⟨6454845006849914517012055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8606460009133219356016073 6454845006849914517012055)
  ·
    refine ⟨9682267510274871775518083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6454845006849914517012055 9682267510274871775518083)
    ·
      refine ⟨14523401265412307663277125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9682267510274871775518083 14523401265412307663277125)
      ·
        refine ⟨2723137737264807686864461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14523401265412307663277125 2723137737264807686864461)
        ·
          refine ⟨1021176651474302882574173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2723137737264807686864461 1021176651474302882574173)
          ·
            refine ⟨382941244302863580965315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1021176651474302882574173 382941244302863580965315)
            ·
              refine ⟨574411866454295371447973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382941244302863580965315 574411866454295371447973)
              ·
                refine ⟨107702224960180382146495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 574411866454295371447973 107702224960180382146495)
                ·
                  rfl

theorem cell19_353952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_353952 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353952 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353952 prefixEnd_353952 := by exact prefixLift 353952
  have htrace : WordTrace (prefixWord ++ tailWord_353952) baseStart_353952 baseEnd_353952 := by
    simpa [prefixWord, tailWord_353952, baseEnd_353952] using wordTrace_append hprefix tailTrace_353952
  have hstable : (prefixWord ++ tailWord_353952).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353952).length < 2 ^ (prefixWord ++ tailWord_353952).sum := by decide
  have hdescent : baseEnd_353952 < baseStart_353952 := by decide
  rcases family_descends (prefixWord ++ tailWord_353952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_353986 : List Nat := [3, 5, 1, 2, 1, 1, 6]
def baseStart_353986 : Nat := 118140960795 + 353986 * 2 ^ 59
def prefixEnd_353986 : Nat := 4983230072969 + 3 ^ 40 * 353986 * 2
def baseEnd_353986 : Nat := 35904190214826125796949

theorem tailTrace_353986 : CollatzResearch.WordTrace tailWord_353986 prefixEnd_353986 35904190214826125796949 := by
  unfold tailWord_353986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227732523894163210190453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8607286730384435227174541 3227732523894163210190453)
  ·
    refine ⟨302599924115077800955355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3227732523894163210190453 302599924115077800955355)
    ·
      refine ⟨453899886172616701433033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302599924115077800955355 453899886172616701433033)
      ·
        refine ⟨340424914629462526074775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453899886172616701433033 340424914629462526074775)
        ·
          refine ⟨510637371944193789112163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340424914629462526074775 510637371944193789112163)
          ·
            refine ⟨765956057916290683668245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510637371944193789112163 765956057916290683668245)
            ·
              refine ⟨35904190214826125796949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 765956057916290683668245 35904190214826125796949)
              ·
                rfl

theorem cell19_353986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_353986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_353986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_353986 prefixEnd_353986 := by exact prefixLift 353986
  have htrace : WordTrace (prefixWord ++ tailWord_353986) baseStart_353986 baseEnd_353986 := by
    simpa [prefixWord, tailWord_353986, baseEnd_353986] using wordTrace_append hprefix tailTrace_353986
  have hstable : (prefixWord ++ tailWord_353986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_353986).length < 2 ^ (prefixWord ++ tailWord_353986).sum := by decide
  have hdescent : baseEnd_353986 < baseStart_353986 := by decide
  rcases family_descends (prefixWord ++ tailWord_353986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354030 : List Nat := [4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_354030 : Nat := 118140960795 + 354030 * 2 ^ 59
def prefixEnd_354030 : Nat := 4983230072969 + 3 ^ 40 * 354030 * 2
def baseEnd_354030 : Nat := 107725959177099312412949

theorem tailTrace_354030 : CollatzResearch.WordTrace tailWord_354030 prefixEnd_354030 107725959177099312412949 := by
  unfold tailWord_354030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614066863427156044420443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8608356604944832236909029 1614066863427156044420443)
  ·
    refine ⟨2421100295140734066630665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1614066863427156044420443 2421100295140734066630665)
    ·
      refine ⟨1815825221355550549972999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2421100295140734066630665 1815825221355550549972999)
      ·
        refine ⟨2723737832033325824959499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1815825221355550549972999 2723737832033325824959499)
        ·
          refine ⟨4085606748049988737439249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723737832033325824959499 4085606748049988737439249)
          ·
            refine ⟨3064205061037491553079437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4085606748049988737439249 3064205061037491553079437)
            ·
              refine ⟨1149076897889059332404789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3064205061037491553079437 1149076897889059332404789)
              ·
                refine ⟨107725959177099312412949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1149076897889059332404789 107725959177099312412949)
                ·
                  rfl

theorem cell19_354030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_354030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354030 prefixEnd_354030 := by exact prefixLift 354030
  have htrace : WordTrace (prefixWord ++ tailWord_354030) baseStart_354030 baseEnd_354030 := by
    simpa [prefixWord, tailWord_354030, baseEnd_354030] using wordTrace_append hprefix tailTrace_354030
  have hstable : (prefixWord ++ tailWord_354030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354030).length < 2 ^ (prefixWord ++ tailWord_354030).sum := by decide
  have hdescent : baseEnd_354030 < baseStart_354030 := by decide
  rcases family_descends (prefixWord ++ tailWord_354030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354051 : List Nat := [1, 1, 1, 3, 2, 2, 9]
def baseStart_354051 : Nat := 118140960795 + 354051 * 2 ^ 59
def prefixEnd_354051 : Nat := 4983230072969 + 3 ^ 40 * 354051 * 2
def baseEnd_354051 : Nat := 35910783052859161982075

theorem tailTrace_354051 : CollatzResearch.WordTrace tailWord_354051 prefixEnd_354051 35910783052859161982075 := by
  unfold tailWord_354051
  simp only [CollatzResearch.WordTrace]
  refine ⟨12913300840341168941878007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8608867226894112627918671 12913300840341168941878007)
  ·
    refine ⟨19369951260511753412817011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12913300840341168941878007 19369951260511753412817011)
    ·
      refine ⟨29054926890767630119225517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19369951260511753412817011 29054926890767630119225517)
      ·
        refine ⟨10895597584037861294709569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29054926890767630119225517 10895597584037861294709569)
        ·
          refine ⟨8171698188028395971032177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10895597584037861294709569 8171698188028395971032177)
          ·
            refine ⟨6128773641021296978274133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8171698188028395971032177 6128773641021296978274133)
            ·
              refine ⟨35910783052859161982075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6128773641021296978274133 35910783052859161982075)
              ·
                rfl

theorem cell19_354051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_354051 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354051 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354051 prefixEnd_354051 := by exact prefixLift 354051
  have htrace : WordTrace (prefixWord ++ tailWord_354051) baseStart_354051 baseEnd_354051 := by
    simpa [prefixWord, tailWord_354051, baseEnd_354051] using wordTrace_append hprefix tailTrace_354051
  have hstable : (prefixWord ++ tailWord_354051).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354051).length < 2 ^ (prefixWord ++ tailWord_354051).sum := by decide
  have hdescent : baseEnd_354051 < baseStart_354051 := by decide
  rcases family_descends (prefixWord ++ tailWord_354051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354066 : List Nat := [3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_354066 : Nat := 118140960795 + 354066 * 2 ^ 59
def prefixEnd_354066 : Nat := 4983230072969 + 3 ^ 40 * 354066 * 2
def baseEnd_354066 : Nat := 107736913431061895612851

theorem tailTrace_354066 : CollatzResearch.WordTrace tailWord_354066 prefixEnd_354066 107736913431061895612851 := by
  unfold tailWord_354066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3228461983821706625918513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8609231956857884335782701 3228461983821706625918513)
  ·
    refine ⟨2421346487866279969438885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3228461983821706625918513 2421346487866279969438885)
    ·
      refine ⟨454002466474927494269791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2421346487866279969438885 454002466474927494269791)
      ·
        refine ⟨681003699712391241404687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454002466474927494269791 681003699712391241404687)
        ·
          refine ⟨1021505549568586862107031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681003699712391241404687 1021505549568586862107031)
          ·
            refine ⟨1532258324352880293160547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021505549568586862107031 1532258324352880293160547)
            ·
              refine ⟨2298387486529320439740821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532258324352880293160547 2298387486529320439740821)
              ·
                refine ⟨107736913431061895612851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2298387486529320439740821 107736913431061895612851)
                ·
                  rfl

theorem cell19_354066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_354066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354066 prefixEnd_354066 := by exact prefixLift 354066
  have htrace : WordTrace (prefixWord ++ tailWord_354066) baseStart_354066 baseEnd_354066 := by
    simpa [prefixWord, tailWord_354066, baseEnd_354066] using wordTrace_append hprefix tailTrace_354066
  have hstable : (prefixWord ++ tailWord_354066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354066).length < 2 ^ (prefixWord ++ tailWord_354066).sum := by decide
  have hdescent : baseEnd_354066 < baseStart_354066 := by decide
  rcases family_descends (prefixWord ++ tailWord_354066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354140 : List Nat := [2, 2, 4, 2, 2, 1, 3, 3]
def baseStart_354140 : Nat := 118140960795 + 354140 * 2 ^ 59
def prefixEnd_354140 : Nat := 4983230072969 + 3 ^ 40 * 354140 * 2
def baseEnd_354140 : Nat := 107759430508651649968205

theorem tailTrace_354140 : CollatzResearch.WordTrace tailWord_354140 prefixEnd_354140 107759430508651649968205 := by
  unfold tailWord_354140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6458273468509368570933937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8611031291345824761245249 6458273468509368570933937)
  ·
    refine ⟨4843705101382026428200453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6458273468509368570933937 4843705101382026428200453)
    ·
      refine ⟨908194706509129955287585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4843705101382026428200453 908194706509129955287585)
      ·
        refine ⟨681146029881847466465689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 908194706509129955287585 681146029881847466465689)
        ·
          refine ⟨510859522411385599849267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681146029881847466465689 510859522411385599849267)
          ·
            refine ⟨766289283617078399773901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510859522411385599849267 766289283617078399773901)
            ·
              refine ⟨287358481356404399915213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 766289283617078399773901 287358481356404399915213)
              ·
                refine ⟨107759430508651649968205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287358481356404399915213 107759430508651649968205)
                ·
                  rfl

theorem cell19_354140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_354140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354140 prefixEnd_354140 := by exact prefixLift 354140
  have htrace : WordTrace (prefixWord ++ tailWord_354140) baseStart_354140 baseEnd_354140 := by
    simpa [prefixWord, tailWord_354140, baseEnd_354140] using wordTrace_append hprefix tailTrace_354140
  have hstable : (prefixWord ++ tailWord_354140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354140).length < 2 ^ (prefixWord ++ tailWord_354140).sum := by decide
  have hdescent : baseEnd_354140 < baseStart_354140 := by decide
  rcases family_descends (prefixWord ++ tailWord_354140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354199 : List Nat := [1, 1, 3, 3, 1, 5, 2, 3]
def baseStart_354199 : Nat := 118140960795 + 354199 * 2 ^ 59
def prefixEnd_354199 : Nat := 4983230072969 + 3 ^ 40 * 354199 * 2
def baseEnd_354199 : Nat := 107777383313756994656933

theorem tailTrace_354199 : CollatzResearch.WordTrace tailWord_354199 prefixEnd_354199 107777383313756994656933 := by
  unfold tailWord_354199
  simp only [CollatzResearch.WordTrace]
  refine ⟨12918698843804990218265651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8612465895869993478843767 12918698843804990218265651)
  ·
    refine ⟨19378048265707485327398477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12918698843804990218265651 19378048265707485327398477)
    ·
      refine ⟨7266768099640306997774429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19378048265707485327398477 7266768099640306997774429)
      ·
        refine ⟨2725038037365115124165411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7266768099640306997774429 2725038037365115124165411)
        ·
          refine ⟨4087557056047672686248117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725038037365115124165411 4087557056047672686248117)
          ·
            refine ⟨383208474004469314335761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4087557056047672686248117 383208474004469314335761)
            ·
              refine ⟨287406355503351985751821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383208474004469314335761 287406355503351985751821)
              ·
                refine ⟨107777383313756994656933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287406355503351985751821 107777383313756994656933)
                ·
                  rfl

theorem cell19_354199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 3].length) (baseStart_354199 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354199 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354199 prefixEnd_354199 := by exact prefixLift 354199
  have htrace : WordTrace (prefixWord ++ tailWord_354199) baseStart_354199 baseEnd_354199 := by
    simpa [prefixWord, tailWord_354199, baseEnd_354199] using wordTrace_append hprefix tailTrace_354199
  have hstable : (prefixWord ++ tailWord_354199).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354199).length < 2 ^ (prefixWord ++ tailWord_354199).sum := by decide
  have hdescent : baseEnd_354199 < baseStart_354199 := by decide
  rcases family_descends (prefixWord ++ tailWord_354199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354201 : List Nat := [1, 2, 1, 2, 1, 3, 6, 3]
def baseStart_354201 : Nat := 118140960795 + 354201 * 2 ^ 59
def prefixEnd_354201 : Nat := 4983230072969 + 3 ^ 40 * 354201 * 2
def baseEnd_354201 : Nat := 107777991883421582612483

theorem tailTrace_354201 : CollatzResearch.WordTrace tailWord_354201 prefixEnd_354201 107777991883421582612483 := by
  unfold tailWord_354201
  simp only [CollatzResearch.WordTrace]
  refine ⟨12918771789797744559838457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8612514526531829706558971 12918771789797744559838457)
  ·
    refine ⟨9689078842348308419878843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12918771789797744559838457 9689078842348308419878843)
    ·
      refine ⟨14533618263522462629818265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9689078842348308419878843 14533618263522462629818265)
      ·
        refine ⟨10900213697641846972363699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14533618263522462629818265 10900213697641846972363699)
        ·
          refine ⟨16350320546462770458545549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10900213697641846972363699 16350320546462770458545549)
          ·
            refine ⟨6131370204923538921954581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16350320546462770458545549 6131370204923538921954581)
            ·
              refine ⟨287407978355790886966621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6131370204923538921954581 287407978355790886966621)
              ·
                refine ⟨107777991883421582612483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287407978355790886966621 107777991883421582612483)
                ·
                  rfl

theorem cell19_354201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_354201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354201 prefixEnd_354201 := by exact prefixLift 354201
  have htrace : WordTrace (prefixWord ++ tailWord_354201) baseStart_354201 baseEnd_354201 := by
    simpa [prefixWord, tailWord_354201, baseEnd_354201] using wordTrace_append hprefix tailTrace_354201
  have hstable : (prefixWord ++ tailWord_354201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354201).length < 2 ^ (prefixWord ++ tailWord_354201).sum := by decide
  have hdescent : baseEnd_354201 < baseStart_354201 := by decide
  rcases family_descends (prefixWord ++ tailWord_354201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354216 : List Nat := [2, 1, 6, 2, 1, 2, 5]
def baseStart_354216 : Nat := 118140960795 + 354216 * 2 ^ 59
def prefixEnd_354216 : Nat := 4983230072969 + 3 ^ 40 * 354216 * 2
def baseEnd_354216 : Nat := 35927518718635330759703

theorem tailTrace_354216 : CollatzResearch.WordTrace tailWord_354216 prefixEnd_354216 35927518718635330759703 := by
  unfold tailWord_354216
  simp only [CollatzResearch.WordTrace]
  refine ⟨6459659442371701060817251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8612879256495601414423001 6459659442371701060817251)
  ·
    refine ⟨9689489163557551591225877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6459659442371701060817251 9689489163557551591225877)
    ·
      refine ⟨454194804541760230838713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9689489163557551591225877 454194804541760230838713)
      ·
        refine ⟨340646103406320173129035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 454194804541760230838713 340646103406320173129035)
        ·
          refine ⟨510969155109480259693553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340646103406320173129035 510969155109480259693553)
          ·
            refine ⟨383226866332110194770165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510969155109480259693553 383226866332110194770165)
            ·
              refine ⟨35927518718635330759703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 383226866332110194770165 35927518718635330759703)
              ·
                rfl

theorem cell19_354216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_354216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354216 prefixEnd_354216 := by exact prefixLift 354216
  have htrace : WordTrace (prefixWord ++ tailWord_354216) baseStart_354216 baseEnd_354216 := by
    simpa [prefixWord, tailWord_354216, baseEnd_354216] using wordTrace_append hprefix tailTrace_354216
  have hstable : (prefixWord ++ tailWord_354216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354216).length < 2 ^ (prefixWord ++ tailWord_354216).sum := by decide
  have hdescent : baseEnd_354216 < baseStart_354216 := by decide
  rcases family_descends (prefixWord ++ tailWord_354216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354279 : List Nat := [1, 1, 5, 2, 10]
def baseStart_354279 : Nat := 118140960795 + 354279 * 2 ^ 59
def prefixEnd_354279 : Nat := 4983230072969 + 3 ^ 40 * 354279 * 2
def baseEnd_354279 : Nat := 3992656522234833810331

theorem tailTrace_354279 : CollatzResearch.WordTrace tailWord_354279 prefixEnd_354279 3992656522234833810331 := by
  unfold tailWord_354279
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921616683515163881177891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8614411122343442587451927 12921616683515163881177891)
  ·
    refine ⟨19382425025272745821766837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12921616683515163881177891 19382425025272745821766837)
    ·
      refine ⟨1817102346119319920790641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19382425025272745821766837 1817102346119319920790641)
      ·
        refine ⟨1362826759589489940592981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1817102346119319920790641 1362826759589489940592981)
        ·
          refine ⟨3992656522234833810331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1362826759589489940592981 3992656522234833810331)
          ·
            rfl

theorem cell19_354279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 10].length) (baseStart_354279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354279 prefixEnd_354279 := by exact prefixLift 354279
  have htrace : WordTrace (prefixWord ++ tailWord_354279) baseStart_354279 baseEnd_354279 := by
    simpa [prefixWord, tailWord_354279, baseEnd_354279] using wordTrace_append hprefix tailTrace_354279
  have hstable : (prefixWord ++ tailWord_354279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354279).length < 2 ^ (prefixWord ++ tailWord_354279).sum := by decide
  have hdescent : baseEnd_354279 < baseStart_354279 := by decide
  rcases family_descends (prefixWord ++ tailWord_354279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354315 : List Nat := [1, 1, 1, 1, 6, 1, 5, 3]
def baseStart_354315 : Nat := 118140960795 + 354315 * 2 ^ 59
def prefixEnd_354315 : Nat := 4983230072969 + 3 ^ 40 * 354315 * 2
def baseEnd_354315 : Nat := 107812680354303096078839

theorem tailTrace_354315 : CollatzResearch.WordTrace tailWord_354315 prefixEnd_354315 107812680354303096078839 := by
  unfold tailWord_354315
  simp only [CollatzResearch.WordTrace]
  refine ⟨12922929711384742029488399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8615286474256494686325599 12922929711384742029488399)
  ·
    refine ⟨19384394567077113044232599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12922929711384742029488399 19384394567077113044232599)
    ·
      refine ⟨29076591850615669566348899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19384394567077113044232599 29076591850615669566348899)
      ·
        refine ⟨43614887775923504349523349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29076591850615669566348899 43614887775923504349523349)
        ·
          refine ⟨2044447864496414266383907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43614887775923504349523349 2044447864496414266383907)
          ·
            refine ⟨3066671796744621399575861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044447864496414266383907 3066671796744621399575861)
            ·
              refine ⟨287500480944808256210237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3066671796744621399575861 287500480944808256210237)
              ·
                refine ⟨107812680354303096078839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287500480944808256210237 107812680354303096078839)
                ·
                  rfl

theorem cell19_354315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 3].length) (baseStart_354315 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354315 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354315 prefixEnd_354315 := by exact prefixLift 354315
  have htrace : WordTrace (prefixWord ++ tailWord_354315) baseStart_354315 baseEnd_354315 := by
    simpa [prefixWord, tailWord_354315, baseEnd_354315] using wordTrace_append hprefix tailTrace_354315
  have hstable : (prefixWord ++ tailWord_354315).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354315).length < 2 ^ (prefixWord ++ tailWord_354315).sum := by decide
  have hdescent : baseEnd_354315 < baseStart_354315 := by decide
  rcases family_descends (prefixWord ++ tailWord_354315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354366 : List Nat := [4, 2, 1, 3, 3, 1, 2, 3]
def baseStart_354366 : Nat := 118140960795 + 354366 * 2 ^ 59
def prefixEnd_354366 : Nat := 4983230072969 + 3 ^ 40 * 354366 * 2
def baseEnd_354366 : Nat := 107828198880750088945367

theorem tailTrace_354366 : CollatzResearch.WordTrace tailWord_354366 prefixEnd_354366 107828198880750088945367 := by
  unfold tailWord_354366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615598729274997217449369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8616526556133318493063301 1615598729274997217449369)
  ·
    refine ⟨1211699046956247913087027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1615598729274997217449369 1211699046956247913087027)
    ·
      refine ⟨1817548570434371869630541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211699046956247913087027 1817548570434371869630541)
      ·
        refine ⟨681580713912889451111453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1817548570434371869630541 681580713912889451111453)
        ·
          refine ⟨255592767717333544166795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 681580713912889451111453 255592767717333544166795)
          ·
            refine ⟨383389151576000316250193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255592767717333544166795 383389151576000316250193)
            ·
              refine ⟨287541863682000237187645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383389151576000316250193 287541863682000237187645)
              ·
                refine ⟨107828198880750088945367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287541863682000237187645 107828198880750088945367)
                ·
                  rfl

theorem cell19_354366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_354366 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354366 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354366 prefixEnd_354366 := by exact prefixLift 354366
  have htrace : WordTrace (prefixWord ++ tailWord_354366) baseStart_354366 baseEnd_354366 := by
    simpa [prefixWord, tailWord_354366, baseEnd_354366] using wordTrace_append hprefix tailTrace_354366
  have hstable : (prefixWord ++ tailWord_354366).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354366).length < 2 ^ (prefixWord ++ tailWord_354366).sum := by decide
  have hdescent : baseEnd_354366 < baseStart_354366 := by decide
  rcases family_descends (prefixWord ++ tailWord_354366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354412 : List Nat := [2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_354412 : Nat := 118140960795 + 354412 * 2 ^ 59
def prefixEnd_354412 : Nat := 4983230072969 + 3 ^ 40 * 354412 * 2
def baseEnd_354412 : Nat := 107842195983035611923019

theorem tailTrace_354412 : CollatzResearch.WordTrace tailWord_354412 prefixEnd_354412 107842195983035611923019 := by
  unfold tailWord_354412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463233796016663797884745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8617645061355551730512993 6463233796016663797884745)
  ·
    refine ⟨4847425347012497848413559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6463233796016663797884745 4847425347012497848413559)
    ·
      refine ⟨7271138020518746772620339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4847425347012497848413559 7271138020518746772620339)
      ·
        refine ⟨10906707030778120158930509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7271138020518746772620339 10906707030778120158930509)
        ·
          refine ⟨4090015136541795059598941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10906707030778120158930509 4090015136541795059598941)
          ·
            refine ⟨1533755676203173147349603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4090015136541795059598941 1533755676203173147349603)
            ·
              refine ⟨2300633514304759721024405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533755676203173147349603 2300633514304759721024405)
              ·
                refine ⟨107842195983035611923019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2300633514304759721024405 107842195983035611923019)
                ·
                  rfl

theorem cell19_354412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_354412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354412 prefixEnd_354412 := by exact prefixLift 354412
  have htrace : WordTrace (prefixWord ++ tailWord_354412) baseStart_354412 baseEnd_354412 := by
    simpa [prefixWord, tailWord_354412, baseEnd_354412] using wordTrace_append hprefix tailTrace_354412
  have hstable : (prefixWord ++ tailWord_354412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354412).length < 2 ^ (prefixWord ++ tailWord_354412).sum := by decide
  have hdescent : baseEnd_354412 < baseStart_354412 := by decide
  rcases family_descends (prefixWord ++ tailWord_354412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354543 : List Nat := [1, 1, 2, 1, 6, 1, 4, 3]
def baseStart_354543 : Nat := 118140960795 + 354543 * 2 ^ 59
def prefixEnd_354543 : Nat := 4983230072969 + 3 ^ 40 * 354543 * 2
def baseEnd_354543 : Nat := 107882057296066123011551

theorem tailTrace_354543 : CollatzResearch.WordTrace tailWord_354543 prefixEnd_354543 107882057296066123011551 := by
  unfold tailWord_354543
  simp only [CollatzResearch.WordTrace]
  refine ⟨12931245554558736968788283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8620830369705824645858855 12931245554558736968788283)
  ·
    refine ⟨19396868331838105453182425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12931245554558736968788283 19396868331838105453182425)
    ·
      refine ⟨14547651248878579089886819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19396868331838105453182425 14547651248878579089886819)
      ·
        refine ⟨21821476873317868634830229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14547651248878579089886819 21821476873317868634830229)
        ·
          refine ⟨1022881728436775092257667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21821476873317868634830229 1022881728436775092257667)
          ·
            refine ⟨1534322592655162638386501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022881728436775092257667 1534322592655162638386501)
            ·
              refine ⟨287685486122842994697469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1534322592655162638386501 287685486122842994697469)
              ·
                refine ⟨107882057296066123011551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287685486122842994697469 107882057296066123011551)
                ·
                  rfl

theorem cell19_354543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_354543 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354543 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354543 prefixEnd_354543 := by exact prefixLift 354543
  have htrace : WordTrace (prefixWord ++ tailWord_354543) baseStart_354543 baseEnd_354543 := by
    simpa [prefixWord, tailWord_354543, baseEnd_354543] using wordTrace_append hprefix tailTrace_354543
  have hstable : (prefixWord ++ tailWord_354543).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354543).length < 2 ^ (prefixWord ++ tailWord_354543).sum := by decide
  have hdescent : baseEnd_354543 < baseStart_354543 := by decide
  rcases family_descends (prefixWord ++ tailWord_354543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354562 : List Nat := [3, 4, 1, 1, 2, 1, 7]
def baseStart_354562 : Nat := 118140960795 + 354562 * 2 ^ 59
def prefixEnd_354562 : Nat := 4983230072969 + 3 ^ 40 * 354562 * 2
def baseEnd_354562 : Nat := 35962612902626569529759

theorem tailTrace_354562 : CollatzResearch.WordTrace tailWord_354562 prefixEnd_354562 35962612902626569529759 := by
  unfold tailWord_354562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3232984635372475803432485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8621292360993268809153293 3232984635372475803432485)
  ·
    refine ⟨606184619132339213143591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3232984635372475803432485 606184619132339213143591)
    ·
      refine ⟨909276928698508819715387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 606184619132339213143591 909276928698508819715387)
      ·
        refine ⟨1363915393047763229573081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 909276928698508819715387 1363915393047763229573081)
        ·
          refine ⟨1022936544785822422179811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1363915393047763229573081 1022936544785822422179811)
          ·
            refine ⟨1534404817178733633269717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022936544785822422179811 1534404817178733633269717)
            ·
              refine ⟨35962612902626569529759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1534404817178733633269717 35962612902626569529759)
              ·
                rfl

theorem cell19_354562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_354562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354562 prefixEnd_354562 := by exact prefixLift 354562
  have htrace : WordTrace (prefixWord ++ tailWord_354562) baseStart_354562 baseEnd_354562 := by
    simpa [prefixWord, tailWord_354562, baseEnd_354562] using wordTrace_append hprefix tailTrace_354562
  have hstable : (prefixWord ++ tailWord_354562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354562).length < 2 ^ (prefixWord ++ tailWord_354562).sum := by decide
  have hdescent : baseEnd_354562 < baseStart_354562 := by decide
  rcases family_descends (prefixWord ++ tailWord_354562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354583 : List Nat := [1, 1, 3, 4, 1, 2, 1, 6]
def baseStart_354583 : Nat := 118140960795 + 354583 * 2 ^ 59
def prefixEnd_354583 : Nat := 4983230072969 + 3 ^ 40 * 354583 * 2
def baseEnd_354583 : Nat := 107894228689357882122553

theorem tailTrace_354583 : CollatzResearch.WordTrace tailWord_354583 prefixEnd_354583 107894228689357882122553 := by
  unfold tailWord_354583
  simp only [CollatzResearch.WordTrace]
  refine ⟨12932704474413823800244403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8621802982942549200162935 12932704474413823800244403)
  ·
    refine ⟨19399056711620735700366605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12932704474413823800244403 19399056711620735700366605)
    ·
      refine ⟨7274646266857775887637477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19399056711620735700366605 7274646266857775887637477)
      ·
        refine ⟨1363996175035832978932027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7274646266857775887637477 1363996175035832978932027)
        ·
          refine ⟨2045994262553749468398041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363996175035832978932027 2045994262553749468398041)
          ·
            refine ⟨1534495696915312101298531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2045994262553749468398041 1534495696915312101298531)
            ·
              refine ⟨2301743545372968151947797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1534495696915312101298531 2301743545372968151947797)
              ·
                refine ⟨107894228689357882122553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2301743545372968151947797 107894228689357882122553)
                ·
                  rfl

theorem cell19_354583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 6].length) (baseStart_354583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354583 prefixEnd_354583 := by exact prefixLift 354583
  have htrace : WordTrace (prefixWord ++ tailWord_354583) baseStart_354583 baseEnd_354583 := by
    simpa [prefixWord, tailWord_354583, baseEnd_354583] using wordTrace_append hprefix tailTrace_354583
  have hstable : (prefixWord ++ tailWord_354583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354583).length < 2 ^ (prefixWord ++ tailWord_354583).sum := by decide
  have hdescent : baseEnd_354583 < baseStart_354583 := by decide
  rcases family_descends (prefixWord ++ tailWord_354583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354640 : List Nat := [2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_354640 : Nat := 118140960795 + 354640 * 2 ^ 59
def prefixEnd_354640 : Nat := 4983230072969 + 3 ^ 40 * 354640 * 2
def baseEnd_354640 : Nat := 107911572924798638855731

theorem tailTrace_354640 : CollatzResearch.WordTrace tailWord_354640 prefixEnd_354640 107911572924798638855731 := by
  unfold tailWord_354640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6467391717603661267534687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8623188956804881690046249 6467391717603661267534687)
  ·
    refine ⟨9701087576405491901302031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6467391717603661267534687 9701087576405491901302031)
    ·
      refine ⟨14551631364608237851953047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9701087576405491901302031 14551631364608237851953047)
      ·
        refine ⟨21827447046912356777929571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14551631364608237851953047 21827447046912356777929571)
        ·
          refine ⟨32741170570368535166894357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21827447046912356777929571 32741170570368535166894357)
          ·
            refine ⟨1534742370486025085948173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32741170570368535166894357 1534742370486025085948173)
            ·
              refine ⟨575528388932259407230565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1534742370486025085948173 575528388932259407230565)
              ·
                refine ⟨107911572924798638855731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 575528388932259407230565 107911572924798638855731)
                ·
                  rfl

theorem cell19_354640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_354640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354640 prefixEnd_354640 := by exact prefixLift 354640
  have htrace : WordTrace (prefixWord ++ tailWord_354640) baseStart_354640 baseEnd_354640 := by
    simpa [prefixWord, tailWord_354640, baseEnd_354640] using wordTrace_append hprefix tailTrace_354640
  have hstable : (prefixWord ++ tailWord_354640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354640).length < 2 ^ (prefixWord ++ tailWord_354640).sum := by decide
  have hdescent : baseEnd_354640 < baseStart_354640 := by decide
  rcases family_descends (prefixWord ++ tailWord_354640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354712 : List Nat := [2, 1, 2, 5, 1, 3, 2, 3]
def baseStart_354712 : Nat := 118140960795 + 354712 * 2 ^ 59
def prefixEnd_354712 : Nat := 4983230072969 + 3 ^ 40 * 354712 * 2
def baseEnd_354712 : Nat := 107933481432723805255535

theorem tailTrace_354712 : CollatzResearch.WordTrace tailWord_354712 prefixEnd_354712 107933481432723805255535 := by
  unfold tailWord_354712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6468704745473239415845195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8624939660630985887793593 6468704745473239415845195)
  ·
    refine ⟨9703057118209859123767793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6468704745473239415845195 9703057118209859123767793)
    ·
      refine ⟨7277292838657394342825845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9703057118209859123767793 7277292838657394342825845)
      ·
        refine ⟨682246203624130719639923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7277292838657394342825845 682246203624130719639923)
        ·
          refine ⟨1023369305436196079459885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682246203624130719639923 1023369305436196079459885)
          ·
            refine ⟨383763489538573529797457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1023369305436196079459885 383763489538573529797457)
            ·
              refine ⟨287822617153930147348093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383763489538573529797457 287822617153930147348093)
              ·
                refine ⟨107933481432723805255535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287822617153930147348093 107933481432723805255535)
                ·
                  rfl

theorem cell19_354712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_354712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354712 prefixEnd_354712 := by exact prefixLift 354712
  have htrace : WordTrace (prefixWord ++ tailWord_354712) baseStart_354712 baseEnd_354712 := by
    simpa [prefixWord, tailWord_354712, baseEnd_354712] using wordTrace_append hprefix tailTrace_354712
  have hstable : (prefixWord ++ tailWord_354712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354712).length < 2 ^ (prefixWord ++ tailWord_354712).sum := by decide
  have hdescent : baseEnd_354712 < baseStart_354712 := by decide
  rcases family_descends (prefixWord ++ tailWord_354712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354714 : List Nat := [3, 1, 1, 4, 1, 2, 4, 3]
def baseStart_354714 : Nat := 118140960795 + 354714 * 2 ^ 59
def prefixEnd_354714 : Nat := 4983230072969 + 3 ^ 40 * 354714 * 2
def baseEnd_354714 : Nat := 107934090002388393211085

theorem tailTrace_354714 : CollatzResearch.WordTrace tailWord_354714 prefixEnd_354714 107934090002388393211085 := by
  unfold tailWord_354714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3234370609234808293315799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8624988291292822115508797 3234370609234808293315799)
  ·
    refine ⟨4851555913852212439973699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3234370609234808293315799 4851555913852212439973699)
    ·
      refine ⟨7277333870778318659960549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4851555913852212439973699 7277333870778318659960549)
      ·
        refine ⟨1364500100770934748742603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7277333870778318659960549 1364500100770934748742603)
        ·
          refine ⟨2046750151156402123113905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364500100770934748742603 2046750151156402123113905)
          ·
            refine ⟨1535062613367301592335429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2046750151156402123113905 1535062613367301592335429)
            ·
              refine ⟨287824240006369048562893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1535062613367301592335429 287824240006369048562893)
              ·
                refine ⟨107934090002388393211085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287824240006369048562893 107934090002388393211085)
                ·
                  rfl

theorem cell19_354714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_354714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354714 prefixEnd_354714 := by exact prefixLift 354714
  have htrace : WordTrace (prefixWord ++ tailWord_354714) baseStart_354714 baseEnd_354714 := by
    simpa [prefixWord, tailWord_354714, baseEnd_354714] using wordTrace_append hprefix tailTrace_354714
  have hstable : (prefixWord ++ tailWord_354714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354714).length < 2 ^ (prefixWord ++ tailWord_354714).sum := by decide
  have hdescent : baseEnd_354714 < baseStart_354714 := by decide
  rcases family_descends (prefixWord ++ tailWord_354714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354773 : List Nat := [1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_354773 : Nat := 118140960795 + 354773 * 2 ^ 59
def prefixEnd_354773 : Nat := 4983230072969 + 3 ^ 40 * 354773 * 2
def baseEnd_354773 : Nat := 107952042807493737899813

theorem tailTrace_354773 : CollatzResearch.WordTrace tailWord_354773 prefixEnd_354773 107952042807493737899813 := by
  unfold tailWord_354773
  simp only [CollatzResearch.WordTrace]
  refine ⟨12939634343725486249660973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8626422895816990833107315 12939634343725486249660973)
  ·
    refine ⟨4852362878897057343622865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12939634343725486249660973 4852362878897057343622865)
    ·
      refine ⟨3639272159172793007717149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4852362878897057343622865 3639272159172793007717149)
      ·
        refine ⟨1364727059689797377893931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3639272159172793007717149 1364727059689797377893931)
        ·
          refine ⟨2047090589534696066840897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364727059689797377893931 2047090589534696066840897)
          ·
            refine ⟨1535317942151022050130673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2047090589534696066840897 1535317942151022050130673)
            ·
              refine ⟨1151488456613266537598005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535317942151022050130673 1151488456613266537598005)
              ·
                refine ⟨107952042807493737899813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1151488456613266537598005 107952042807493737899813)
                ·
                  rfl

theorem cell19_354773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_354773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354773 prefixEnd_354773 := by exact prefixLift 354773
  have htrace : WordTrace (prefixWord ++ tailWord_354773) baseStart_354773 baseEnd_354773 := by
    simpa [prefixWord, tailWord_354773, baseEnd_354773] using wordTrace_append hprefix tailTrace_354773
  have hstable : (prefixWord ++ tailWord_354773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354773).length < 2 ^ (prefixWord ++ tailWord_354773).sum := by decide
  have hdescent : baseEnd_354773 < baseStart_354773 := by decide
  rcases family_descends (prefixWord ++ tailWord_354773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354805 : List Nat := [1, 3, 5, 1, 3, 1, 1, 4]
def baseStart_354805 : Nat := 118140960795 + 354805 * 2 ^ 59
def prefixEnd_354805 : Nat := 4983230072969 + 3 ^ 40 * 354805 * 2
def baseEnd_354805 : Nat := 107961779922127145188615

theorem tailTrace_354805 : CollatzResearch.WordTrace tailWord_354805 prefixEnd_354805 107961779922127145188615 := by
  unfold tailWord_354805
  simp only [CollatzResearch.WordTrace]
  refine ⟨12940801479609555714825869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8627200986406370476550579 12940801479609555714825869)
  ·
    refine ⟨4852800554853583393059701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12940801479609555714825869 4852800554853583393059701)
    ·
      refine ⟨454950052017523443099347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4852800554853583393059701 454950052017523443099347)
      ·
        refine ⟨682425078026285164649021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454950052017523443099347 682425078026285164649021)
        ·
          refine ⟨255909404259856936743383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 682425078026285164649021 255909404259856936743383)
          ·
            refine ⟨383864106389785405115075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255909404259856936743383 383864106389785405115075)
            ·
              refine ⟨575796159584678107672613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383864106389785405115075 575796159584678107672613)
              ·
                refine ⟨107961779922127145188615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 575796159584678107672613 107961779922127145188615)
                ·
                  rfl

theorem cell19_354805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 4].length) (baseStart_354805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354805 prefixEnd_354805 := by exact prefixLift 354805
  have htrace : WordTrace (prefixWord ++ tailWord_354805) baseStart_354805 baseEnd_354805 := by
    simpa [prefixWord, tailWord_354805, baseEnd_354805] using wordTrace_append hprefix tailTrace_354805
  have hstable : (prefixWord ++ tailWord_354805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354805).length < 2 ^ (prefixWord ++ tailWord_354805).sum := by decide
  have hdescent : baseEnd_354805 < baseStart_354805 := by decide
  rcases family_descends (prefixWord ++ tailWord_354805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354822 : List Nat := [6, 2, 1, 1, 1, 2, 3, 3]
def baseStart_354822 : Nat := 118140960795 + 354822 * 2 ^ 59
def prefixEnd_354822 : Nat := 4983230072969 + 3 ^ 40 * 354822 * 2
def baseEnd_354822 : Nat := 107966952764276142810791

theorem tailTrace_354822 : CollatzResearch.WordTrace tailWord_354822 prefixEnd_354822 107966952764276142810791 := by
  unfold tailWord_354822
  simp only [CollatzResearch.WordTrace]
  refine ⟨404419422517123988068585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8627614347031978412129813 404419422517123988068585)
  ·
    refine ⟨303314566887842991051439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 404419422517123988068585 303314566887842991051439)
    ·
      refine ⟨454971850331764486577159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 303314566887842991051439 454971850331764486577159)
      ·
        refine ⟨682457775497646729865739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454971850331764486577159 682457775497646729865739)
        ·
          refine ⟨1023686663246470094798609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682457775497646729865739 1023686663246470094798609)
          ·
            refine ⟨767764997434852571098957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023686663246470094798609 767764997434852571098957)
            ·
              refine ⟨287911874038069714162109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 767764997434852571098957 287911874038069714162109)
              ·
                refine ⟨107966952764276142810791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287911874038069714162109 107966952764276142810791)
                ·
                  rfl

theorem cell19_354822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_354822 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354822 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354822 prefixEnd_354822 := by exact prefixLift 354822
  have htrace : WordTrace (prefixWord ++ tailWord_354822) baseStart_354822 baseEnd_354822 := by
    simpa [prefixWord, tailWord_354822, baseEnd_354822] using wordTrace_append hprefix tailTrace_354822
  have hstable : (prefixWord ++ tailWord_354822).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354822).length < 2 ^ (prefixWord ++ tailWord_354822).sum := by decide
  have hdescent : baseEnd_354822 < baseStart_354822 := by decide
  rcases family_descends (prefixWord ++ tailWord_354822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354828 : List Nat := [2, 2, 1, 2, 4, 2, 3, 3]
def baseStart_354828 : Nat := 118140960795 + 354828 * 2 ^ 59
def prefixEnd_354828 : Nat := 4983230072969 + 3 ^ 40 * 354828 * 2
def baseEnd_354828 : Nat := 107968778473269906677441

theorem tailTrace_354828 : CollatzResearch.WordTrace tailWord_354828 prefixEnd_354828 107968778473269906677441 := by
  unfold tailWord_354828
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470820179263115321456569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8627760239017487095275425 6470820179263115321456569)
  ·
    refine ⟨4853115134447336491092427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6470820179263115321456569 4853115134447336491092427)
    ·
      refine ⟨7279672701671004736638641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4853115134447336491092427 7279672701671004736638641)
      ·
        refine ⟨5459754526253253552478981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7279672701671004736638641 5459754526253253552478981)
        ·
          refine ⟨1023703973672485041089809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5459754526253253552478981 1023703973672485041089809)
          ·
            refine ⟨767777980254363780817357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023703973672485041089809 767777980254363780817357)
            ·
              refine ⟨287916742595386417806509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 767777980254363780817357 287916742595386417806509)
              ·
                refine ⟨107968778473269906677441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287916742595386417806509 107968778473269906677441)
                ·
                  rfl

theorem cell19_354828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_354828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354828 prefixEnd_354828 := by exact prefixLift 354828
  have htrace : WordTrace (prefixWord ++ tailWord_354828) baseStart_354828 baseEnd_354828 := by
    simpa [prefixWord, tailWord_354828, baseEnd_354828] using wordTrace_append hprefix tailTrace_354828
  have hstable : (prefixWord ++ tailWord_354828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354828).length < 2 ^ (prefixWord ++ tailWord_354828).sum := by decide
  have hdescent : baseEnd_354828 < baseStart_354828 := by decide
  rcases family_descends (prefixWord ++ tailWord_354828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354885 : List Nat := [1, 3, 1, 1, 1, 7, 2, 3]
def baseStart_354885 : Nat := 118140960795 + 354885 * 2 ^ 59
def prefixEnd_354885 : Nat := 4983230072969 + 3 ^ 40 * 354885 * 2
def baseEnd_354885 : Nat := 107986122708710663410619

theorem tailTrace_354885 : CollatzResearch.WordTrace tailWord_354885 prefixEnd_354885 107986122708710663410619 := by
  unfold tailWord_354885
  simp only [CollatzResearch.WordTrace]
  refine ⟨12943719319319729377738109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8629146212879819585158739 12943719319319729377738109)
  ·
    refine ⟨4853894744744898516651791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12943719319319729377738109 4853894744744898516651791)
    ·
      refine ⟨7280842117117347774977687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4853894744744898516651791 7280842117117347774977687)
      ·
        refine ⟨10921263175676021662466531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7280842117117347774977687 10921263175676021662466531)
        ·
          refine ⟨16381894763514032493699797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10921263175676021662466531 16381894763514032493699797)
          ·
            refine ⟨383950658519860136571089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16381894763514032493699797 383950658519860136571089)
            ·
              refine ⟨287962993889895102428317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383950658519860136571089 287962993889895102428317)
              ·
                refine ⟨107986122708710663410619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287962993889895102428317 107986122708710663410619)
                ·
                  rfl

theorem cell19_354885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_354885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354885 prefixEnd_354885 := by exact prefixLift 354885
  have htrace : WordTrace (prefixWord ++ tailWord_354885) baseStart_354885 baseEnd_354885 := by
    simpa [prefixWord, tailWord_354885, baseEnd_354885] using wordTrace_append hprefix tailTrace_354885
  have hstable : (prefixWord ++ tailWord_354885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354885).length < 2 ^ (prefixWord ++ tailWord_354885).sum := by decide
  have hdescent : baseEnd_354885 < baseStart_354885 := by decide
  rcases family_descends (prefixWord ++ tailWord_354885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354887 : List Nat := [1, 1, 4, 1, 4, 2, 1, 5]
def baseStart_354887 : Nat := 118140960795 + 354887 * 2 ^ 59
def prefixEnd_354887 : Nat := 4983230072969 + 3 ^ 40 * 354887 * 2
def baseEnd_354887 : Nat := 107986731278375251366169

theorem tailTrace_354887 : CollatzResearch.WordTrace tailWord_354887 prefixEnd_354887 107986731278375251366169 := by
  unfold tailWord_354887
  simp only [CollatzResearch.WordTrace]
  refine ⟨12943792265312483719310915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8629194843541655812873943 12943792265312483719310915)
  ·
    refine ⟨19415688397968725578966373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12943792265312483719310915 19415688397968725578966373)
    ·
      refine ⟨3640441574619136046056195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19415688397968725578966373 3640441574619136046056195)
      ·
        refine ⟨5460662361928704069084293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640441574619136046056195 5460662361928704069084293)
        ·
          refine ⟨1023874192861632012953305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5460662361928704069084293 1023874192861632012953305)
          ·
            refine ⟨767905644646224009714979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023874192861632012953305 767905644646224009714979)
            ·
              refine ⟨1151858466969336014572469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767905644646224009714979 1151858466969336014572469)
              ·
                refine ⟨107986731278375251366169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1151858466969336014572469 107986731278375251366169)
                ·
                  rfl

theorem cell19_354887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_354887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354887 prefixEnd_354887 := by exact prefixLift 354887
  have htrace : WordTrace (prefixWord ++ tailWord_354887) baseStart_354887 baseEnd_354887 := by
    simpa [prefixWord, tailWord_354887, baseEnd_354887] using wordTrace_append hprefix tailTrace_354887
  have hstable : (prefixWord ++ tailWord_354887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354887).length < 2 ^ (prefixWord ++ tailWord_354887).sum := by decide
  have hdescent : baseEnd_354887 < baseStart_354887 := by decide
  rcases family_descends (prefixWord ++ tailWord_354887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354925 : List Nat := [1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_354925 : Nat := 118140960795 + 354925 * 2 ^ 59
def prefixEnd_354925 : Nat := 4983230072969 + 3 ^ 40 * 354925 * 2
def baseEnd_354925 : Nat := 107998294102002422521621

theorem tailTrace_354925 : CollatzResearch.WordTrace tailWord_354925 prefixEnd_354925 107998294102002422521621 := by
  unfold tailWord_354925
  simp only [CollatzResearch.WordTrace]
  refine ⟨12945178239174816209194229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8630118826116544139462819 12945178239174816209194229)
  ·
    refine ⟨1213610459922639019611959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12945178239174816209194229 1213610459922639019611959)
    ·
      refine ⟨1820415689883958529417939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213610459922639019611959 1820415689883958529417939)
      ·
        refine ⟨2730623534825937794126909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820415689883958529417939 2730623534825937794126909)
        ·
          refine ⟨1023983825559726672797591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2730623534825937794126909 1023983825559726672797591)
          ·
            refine ⟨1535975738339590009196387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023983825559726672797591 1535975738339590009196387)
            ·
              refine ⟨2303963607509385013794581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535975738339590009196387 2303963607509385013794581)
              ·
                refine ⟨107998294102002422521621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2303963607509385013794581 107998294102002422521621)
                ·
                  rfl

theorem cell19_354925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_354925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354925 prefixEnd_354925 := by exact prefixLift 354925
  have htrace : WordTrace (prefixWord ++ tailWord_354925) baseStart_354925 baseEnd_354925 := by
    simpa [prefixWord, tailWord_354925, baseEnd_354925] using wordTrace_append hprefix tailTrace_354925
  have hstable : (prefixWord ++ tailWord_354925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354925).length < 2 ^ (prefixWord ++ tailWord_354925).sum := by decide
  have hdescent : baseEnd_354925 < baseStart_354925 := by decide
  rcases family_descends (prefixWord ++ tailWord_354925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354927 : List Nat := [1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_354927 : Nat := 118140960795 + 354927 * 2 ^ 59
def prefixEnd_354927 : Nat := 4983230072969 + 3 ^ 40 * 354927 * 2
def baseEnd_354927 : Nat := 107998902671667010477171

theorem tailTrace_354927 : CollatzResearch.WordTrace tailWord_354927 prefixEnd_354927 107998902671667010477171 := by
  unfold tailWord_354927
  simp only [CollatzResearch.WordTrace]
  refine ⟨12945251185167570550767035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8630167456778380367178023 12945251185167570550767035)
  ·
    refine ⟨19417876777751355826150553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12945251185167570550767035 19417876777751355826150553)
    ·
      refine ⟨14563407583313516869612915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19417876777751355826150553 14563407583313516869612915)
      ·
        refine ⟨21845111374970275304419373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14563407583313516869612915 21845111374970275304419373)
        ·
          refine ⟨8191916765613853239157265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21845111374970275304419373 8191916765613853239157265)
          ·
            refine ⟨6143937574210389929367949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8191916765613853239157265 6143937574210389929367949)
            ·
              refine ⟨2303976590328896223512981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6143937574210389929367949 2303976590328896223512981)
              ·
                refine ⟨107998902671667010477171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2303976590328896223512981 107998902671667010477171)
                ·
                  rfl

theorem cell19_354927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_354927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354927 prefixEnd_354927 := by exact prefixLift 354927
  have htrace : WordTrace (prefixWord ++ tailWord_354927) baseStart_354927 baseEnd_354927 := by
    simpa [prefixWord, tailWord_354927, baseEnd_354927] using wordTrace_append hprefix tailTrace_354927
  have hstable : (prefixWord ++ tailWord_354927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354927).length < 2 ^ (prefixWord ++ tailWord_354927).sum := by decide
  have hdescent : baseEnd_354927 < baseStart_354927 := by decide
  rcases family_descends (prefixWord ++ tailWord_354927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_354999 : List Nat := [1, 1, 3, 1, 6, 1, 3, 3]
def baseStart_354999 : Nat := 118140960795 + 354999 * 2 ^ 59
def prefixEnd_354999 : Nat := 4983230072969 + 3 ^ 40 * 354999 * 2
def baseEnd_354999 : Nat := 108020811179592176876975

theorem tailTrace_354999 : CollatzResearch.WordTrace tailWord_354999 prefixEnd_354999 108020811179592176876975 := by
  unfold tailWord_354999
  simp only [CollatzResearch.WordTrace]
  refine ⟨12947877240906726847388051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8631918160604484564925367 12947877240906726847388051)
  ·
    refine ⟨19421815861360090271082077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12947877240906726847388051 19421815861360090271082077)
    ·
      refine ⟨7283180948010033851655779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19421815861360090271082077 7283180948010033851655779)
      ·
        refine ⟨10924771422015050777483669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7283180948010033851655779 10924771422015050777483669)
        ·
          refine ⟨512098660406955505194547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10924771422015050777483669 512098660406955505194547)
          ·
            refine ⟨768147990610433257791821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512098660406955505194547 768147990610433257791821)
            ·
              refine ⟨288055496478912471671933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 768147990610433257791821 288055496478912471671933)
              ·
                refine ⟨108020811179592176876975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288055496478912471671933 108020811179592176876975)
                ·
                  rfl

theorem cell19_354999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 3].length) (baseStart_354999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_354999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_354999 prefixEnd_354999 := by exact prefixLift 354999
  have htrace : WordTrace (prefixWord ++ tailWord_354999) baseStart_354999 baseEnd_354999 := by
    simpa [prefixWord, tailWord_354999, baseEnd_354999] using wordTrace_append hprefix tailTrace_354999
  have hstable : (prefixWord ++ tailWord_354999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_354999).length < 2 ^ (prefixWord ++ tailWord_354999).sum := by decide
  have hdescent : baseEnd_354999 < baseStart_354999 := by decide
  rcases family_descends (prefixWord ++ tailWord_354999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355020 : List Nat := [2, 2, 1, 5, 1, 2, 6]
def baseStart_355020 : Nat := 118140960795 + 355020 * 2 ^ 59
def prefixEnd_355020 : Nat := 4983230072969 + 3 ^ 40 * 355020 * 2
def baseEnd_355020 : Nat := 36009067053690116803417

theorem tailTrace_355020 : CollatzResearch.WordTrace tailWord_355020 prefixEnd_355020 36009067053690116803417 := by
  unfold tailWord_355020
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474321586915323716951257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8632428782553764955935009 6474321586915323716951257)
  ·
    refine ⟨4855741190186492787713443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6474321586915323716951257 4855741190186492787713443)
    ·
      refine ⟨7283611785279739181570165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4855741190186492787713443 7283611785279739181570165)
      ·
        refine ⟨682838604869975548272203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7283611785279739181570165 682838604869975548272203)
        ·
          refine ⟨1024257907304963322408305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682838604869975548272203 1024257907304963322408305)
          ·
            refine ⟨768193430478722491806229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024257907304963322408305 768193430478722491806229)
            ·
              refine ⟨36009067053690116803417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 768193430478722491806229 36009067053690116803417)
              ·
                rfl

theorem cell19_355020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_355020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355020 prefixEnd_355020 := by exact prefixLift 355020
  have htrace : WordTrace (prefixWord ++ tailWord_355020) baseStart_355020 baseEnd_355020 := by
    simpa [prefixWord, tailWord_355020, baseEnd_355020] using wordTrace_append hprefix tailTrace_355020
  have hstable : (prefixWord ++ tailWord_355020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355020).length < 2 ^ (prefixWord ++ tailWord_355020).sum := by decide
  have hdescent : baseEnd_355020 < baseStart_355020 := by decide
  rcases family_descends (prefixWord ++ tailWord_355020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355058 : List Nat := [3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_355058 : Nat := 118140960795 + 355058 * 2 ^ 59
def prefixEnd_355058 : Nat := 4983230072969 + 3 ^ 40 * 355058 * 2
def baseEnd_355058 : Nat := 108038763984697521565703

theorem tailTrace_355058 : CollatzResearch.WordTrace tailWord_355058 prefixEnd_355058 108038763984697521565703 := by
  unfold tailWord_355058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237507286923244980946457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8633352765128653282523885 3237507286923244980946457)
  ·
    refine ⟨2428130465192433735709843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3237507286923244980946457 2428130465192433735709843)
    ·
      refine ⟨3642195697788650603564765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2428130465192433735709843 3642195697788650603564765)
      ·
        refine ⟨1365823386670743976336787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3642195697788650603564765 1365823386670743976336787)
        ·
          refine ⟨2048735080006115964505181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365823386670743976336787 2048735080006115964505181)
          ·
            refine ⟨768275655002293486689443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2048735080006115964505181 768275655002293486689443)
            ·
              refine ⟨1152413482503440230034165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768275655002293486689443 1152413482503440230034165)
              ·
                refine ⟨108038763984697521565703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1152413482503440230034165 108038763984697521565703)
                ·
                  rfl

theorem cell19_355058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_355058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355058 prefixEnd_355058 := by exact prefixLift 355058
  have htrace : WordTrace (prefixWord ++ tailWord_355058) baseStart_355058 baseEnd_355058 := by
    simpa [prefixWord, tailWord_355058, baseEnd_355058] using wordTrace_append hprefix tailTrace_355058
  have hstable : (prefixWord ++ tailWord_355058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355058).length < 2 ^ (prefixWord ++ tailWord_355058).sum := by decide
  have hdescent : baseEnd_355058 < baseStart_355058 := by decide
  rcases family_descends (prefixWord ++ tailWord_355058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355134 : List Nat := [4, 2, 1, 2, 3, 7]
def baseStart_355134 : Nat := 118140960795 + 355134 * 2 ^ 59
def prefixEnd_355134 : Nat := 4983230072969 + 3 ^ 40 * 355134 * 2
def baseEnd_355134 : Nat := 12006876625772429319623

theorem tailTrace_355134 : CollatzResearch.WordTrace tailWord_355134 prefixEnd_355134 12006876625772429319623 := by
  unfold tailWord_355134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619100136927205612944057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8635200730278429935701637 1619100136927205612944057)
  ·
    refine ⟨1214325102695404209708043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1619100136927205612944057 1214325102695404209708043)
    ·
      refine ⟨1821487654043106314562065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1214325102695404209708043 1821487654043106314562065)
      ·
        refine ⟨1366115740532329735921549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1821487654043106314562065 1366115740532329735921549)
        ·
          refine ⟨512293402699623650970581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1366115740532329735921549 512293402699623650970581)
          ·
            refine ⟨12006876625772429319623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 512293402699623650970581 12006876625772429319623)
            ·
              rfl

theorem cell19_355134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 7].length) (baseStart_355134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355134 prefixEnd_355134 := by exact prefixLift 355134
  have htrace : WordTrace (prefixWord ++ tailWord_355134) baseStart_355134 baseEnd_355134 := by
    simpa [prefixWord, tailWord_355134, baseEnd_355134] using wordTrace_append hprefix tailTrace_355134
  have hstable : (prefixWord ++ tailWord_355134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355134).length < 2 ^ (prefixWord ++ tailWord_355134).sum := by decide
  have hdescent : baseEnd_355134 < baseStart_355134 := by decide
  rcases family_descends (prefixWord ++ tailWord_355134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355149 : List Nat := [1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_355149 : Nat := 118140960795 + 355149 * 2 ^ 59
def prefixEnd_355149 : Nat := 4983230072969 + 3 ^ 40 * 355149 * 2
def baseEnd_355149 : Nat := 108066453904436273543233

theorem tailTrace_355149 : CollatzResearch.WordTrace tailWord_355149 prefixEnd_355149 108066453904436273543233 := by
  unfold tailWord_355149
  simp only [CollatzResearch.WordTrace]
  refine ⟨12953348190363302465348501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8635565460242201643565667 12953348190363302465348501)
  ·
    refine ⟨607188196423279803063211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12953348190363302465348501 607188196423279803063211)
    ·
      refine ⟨910782294634919704594817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607188196423279803063211 910782294634919704594817)
      ·
        refine ⟨683086720976189778446113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 910782294634919704594817 683086720976189778446113)
        ·
          refine ⟨512315040732142333834585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 683086720976189778446113 512315040732142333834585)
          ·
            refine ⟨384236280549106750375939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512315040732142333834585 384236280549106750375939)
            ·
              refine ⟨576354420823660125563909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384236280549106750375939 576354420823660125563909)
              ·
                refine ⟨108066453904436273543233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576354420823660125563909 108066453904436273543233)
                ·
                  rfl

theorem cell19_355149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_355149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355149 prefixEnd_355149 := by exact prefixLift 355149
  have htrace : WordTrace (prefixWord ++ tailWord_355149) baseStart_355149 baseEnd_355149 := by
    simpa [prefixWord, tailWord_355149, baseEnd_355149] using wordTrace_append hprefix tailTrace_355149
  have hstable : (prefixWord ++ tailWord_355149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355149).length < 2 ^ (prefixWord ++ tailWord_355149).sum := by decide
  have hdescent : baseEnd_355149 < baseStart_355149 := by decide
  rcases family_descends (prefixWord ++ tailWord_355149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355193 : List Nat := [1, 2, 1, 3, 2, 4, 6]
def baseStart_355193 : Nat := 118140960795 + 355193 * 2 ^ 59
def prefixEnd_355193 : Nat := 4983230072969 + 3 ^ 40 * 355193 * 2
def baseEnd_355193 : Nat := 36026614145685736188445

theorem tailTrace_355193 : CollatzResearch.WordTrace tailWord_355193 prefixEnd_355193 36026614145685736188445 := by
  unfold tailWord_355193
  simp only [CollatzResearch.WordTrace]
  refine ⟨12954953002203897979950233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8636635334802598653300155 12954953002203897979950233)
  ·
    refine ⟨9716214751652923484962675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12954953002203897979950233 9716214751652923484962675)
    ·
      refine ⟨14574322127479385227444013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9716214751652923484962675 14574322127479385227444013)
      ·
        refine ⟨5465370797804769460291505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14574322127479385227444013 5465370797804769460291505)
        ·
          refine ⟨4099028098353577095218629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5465370797804769460291505 4099028098353577095218629)
          ·
            refine ⟨768567768441295705353493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4099028098353577095218629 768567768441295705353493)
            ·
              refine ⟨36026614145685736188445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 768567768441295705353493 36026614145685736188445)
              ·
                rfl

theorem cell19_355193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_355193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355193 prefixEnd_355193 := by exact prefixLift 355193
  have htrace : WordTrace (prefixWord ++ tailWord_355193) baseStart_355193 baseEnd_355193 := by
    simpa [prefixWord, tailWord_355193, baseEnd_355193] using wordTrace_append hprefix tailTrace_355193
  have hstable : (prefixWord ++ tailWord_355193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355193).length < 2 ^ (prefixWord ++ tailWord_355193).sum := by decide
  have hdescent : baseEnd_355193 < baseStart_355193 := by decide
  rcases family_descends (prefixWord ++ tailWord_355193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355288 : List Nat := [2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_355288 : Nat := 118140960795 + 355288 * 2 ^ 59
def prefixEnd_355288 : Nat := 4983230072969 + 3 ^ 40 * 355288 * 2
def baseEnd_355288 : Nat := 108108749496125136453965

theorem tailTrace_355288 : CollatzResearch.WordTrace tailWord_355288 prefixEnd_355288 108108749496125136453965 := by
  unfold tailWord_355288
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479208968429864602329259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8638945291239819469772345 6479208968429864602329259)
  ·
    refine ⟨9718813452644796903493889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6479208968429864602329259 9718813452644796903493889)
    ·
      refine ⟨7289110089483597677620417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9718813452644796903493889 7289110089483597677620417)
      ·
        refine ⟨5466832567112698258215313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7289110089483597677620417 5466832567112698258215313)
        ·
          refine ⟨4100124425334523693661485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5466832567112698258215313 4100124425334523693661485)
          ·
            refine ⟨1537546659500446385123057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4100124425334523693661485 1537546659500446385123057)
            ·
              refine ⟨1153159994625334788842293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537546659500446385123057 1153159994625334788842293)
              ·
                refine ⟨108108749496125136453965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1153159994625334788842293 108108749496125136453965)
                ·
                  rfl

theorem cell19_355288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_355288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355288 prefixEnd_355288 := by exact prefixLift 355288
  have htrace : WordTrace (prefixWord ++ tailWord_355288) baseStart_355288 baseEnd_355288 := by
    simpa [prefixWord, tailWord_355288, baseEnd_355288] using wordTrace_append hprefix tailTrace_355288
  have hstable : (prefixWord ++ tailWord_355288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355288).length < 2 ^ (prefixWord ++ tailWord_355288).sum := by decide
  have hdescent : baseEnd_355288 < baseStart_355288 := by decide
  rcases family_descends (prefixWord ++ tailWord_355288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355316 : List Nat := [2, 6, 2, 1, 1, 2, 1, 4]
def baseStart_355316 : Nat := 118140960795 + 355316 * 2 ^ 59
def prefixEnd_355316 : Nat := 4983230072969 + 3 ^ 40 * 355316 * 2
def baseEnd_355316 : Nat := 108117269471429367831667

theorem tailTrace_355316 : CollatzResearch.WordTrace tailWord_355316 prefixEnd_355316 108117269471429367831667 := by
  unfold tailWord_355316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479719590379144993338901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8639626120505526657785201 6479719590379144993338901)
  ·
    refine ⟨303736855799022421562761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6479719590379144993338901 303736855799022421562761)
    ·
      refine ⟨227802641849266816172071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 303736855799022421562761 227802641849266816172071)
      ·
        refine ⟨341703962773900224258107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227802641849266816172071 341703962773900224258107)
        ·
          refine ⟨512555944160850336387161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341703962773900224258107 512555944160850336387161)
          ·
            refine ⟨384416958120637752290371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 512555944160850336387161 384416958120637752290371)
            ·
              refine ⟨576625437180956628435557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384416958120637752290371 576625437180956628435557)
              ·
                refine ⟨108117269471429367831667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576625437180956628435557 108117269471429367831667)
                ·
                  rfl

theorem cell19_355316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_355316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355316 prefixEnd_355316 := by exact prefixLift 355316
  have htrace : WordTrace (prefixWord ++ tailWord_355316) baseStart_355316 baseEnd_355316 := by
    simpa [prefixWord, tailWord_355316, baseEnd_355316] using wordTrace_append hprefix tailTrace_355316
  have hstable : (prefixWord ++ tailWord_355316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355316).length < 2 ^ (prefixWord ++ tailWord_355316).sum := by decide
  have hdescent : baseEnd_355316 < baseStart_355316 := by decide
  rcases family_descends (prefixWord ++ tailWord_355316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355324 : List Nat := [2, 2, 2, 1, 2, 5, 1, 4]
def baseStart_355324 : Nat := 118140960795 + 355324 * 2 ^ 59
def prefixEnd_355324 : Nat := 4983230072969 + 3 ^ 40 * 355324 * 2
def baseEnd_355324 : Nat := 108119703750087719653867

theorem tailTrace_355324 : CollatzResearch.WordTrace tailWord_355324 prefixEnd_355324 108119703750087719653867 := by
  unfold tailWord_355324
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479865482364653676484513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8639820643152871568646017 6479865482364653676484513)
  ·
    refine ⟨4859899111773490257363385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6479865482364653676484513 4859899111773490257363385)
    ·
      refine ⟨3644924333830117693022539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4859899111773490257363385 3644924333830117693022539)
      ·
        refine ⟨5467386500745176539533809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3644924333830117693022539 5467386500745176539533809)
        ·
          refine ⟨4100539875558882404650357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5467386500745176539533809 4100539875558882404650357)
          ·
            refine ⟨384425613333645225435971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4100539875558882404650357 384425613333645225435971)
            ·
              refine ⟨576638420000467838153957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384425613333645225435971 576638420000467838153957)
              ·
                refine ⟨108119703750087719653867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576638420000467838153957 108119703750087719653867)
                ·
                  rfl

theorem cell19_355324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_355324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355324 prefixEnd_355324 := by exact prefixLift 355324
  have htrace : WordTrace (prefixWord ++ tailWord_355324) baseStart_355324 baseEnd_355324 := by
    simpa [prefixWord, tailWord_355324, baseEnd_355324] using wordTrace_append hprefix tailTrace_355324
  have hstable : (prefixWord ++ tailWord_355324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355324).length < 2 ^ (prefixWord ++ tailWord_355324).sum := by decide
  have hdescent : baseEnd_355324 < baseStart_355324 := by decide
  rcases family_descends (prefixWord ++ tailWord_355324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355398 : List Nat := [6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_355398 : Nat := 118140960795 + 355398 * 2 ^ 59
def prefixEnd_355398 : Nat := 4983230072969 + 3 ^ 40 * 355398 * 2
def baseEnd_355398 : Nat := 108142220827677474009221

theorem tailTrace_355398 : CollatzResearch.WordTrace tailWord_355398 prefixEnd_355398 108142220827677474009221 := by
  unfold tailWord_355398
  simp only [CollatzResearch.WordTrace]
  refine ⟨405075936451913062223839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8641619977640811994108565 405075936451913062223839)
  ·
    refine ⟨607613904677869593335759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 405075936451913062223839 607613904677869593335759)
    ·
      refine ⟨911420857016804390003639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607613904677869593335759 911420857016804390003639)
      ·
        refine ⟨1367131285525206585005459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911420857016804390003639 1367131285525206585005459)
        ·
          refine ⟨2050696928287809877508189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367131285525206585005459 2050696928287809877508189)
          ·
            refine ⟨769011348107928704065571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2050696928287809877508189 769011348107928704065571)
            ·
              refine ⟨1153517022161893056098357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769011348107928704065571 1153517022161893056098357)
              ·
                refine ⟨108142220827677474009221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1153517022161893056098357 108142220827677474009221)
                ·
                  rfl

theorem cell19_355398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_355398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355398 prefixEnd_355398 := by exact prefixLift 355398
  have htrace : WordTrace (prefixWord ++ tailWord_355398) baseStart_355398 baseEnd_355398 := by
    simpa [prefixWord, tailWord_355398, baseEnd_355398] using wordTrace_append hprefix tailTrace_355398
  have hstable : (prefixWord ++ tailWord_355398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355398).length < 2 ^ (prefixWord ++ tailWord_355398).sum := by decide
  have hdescent : baseEnd_355398 < baseStart_355398 := by decide
  rcases family_descends (prefixWord ++ tailWord_355398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355438 : List Nat := [4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_355438 : Nat := 118140960795 + 355438 * 2 ^ 59
def prefixEnd_355438 : Nat := 4983230072969 + 3 ^ 40 * 355438 * 2
def baseEnd_355438 : Nat := 108154392220969233120223

theorem tailTrace_355438 : CollatzResearch.WordTrace tailWord_355438 prefixEnd_355438 108154392220969233120223 := by
  unfold tailWord_355438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620486110789538102827371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8642592590877536548412645 1620486110789538102827371)
  ·
    refine ⟨2430729166184307154241057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1620486110789538102827371 2430729166184307154241057)
    ·
      refine ⟨1823046874638230365680793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2430729166184307154241057 1823046874638230365680793)
      ·
        refine ⟨1367285155978672774260595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1823046874638230365680793 1367285155978672774260595)
        ·
          refine ⟨2050927733968009161390893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367285155978672774260595 2050927733968009161390893)
          ·
            refine ⟨769097900238003435521585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2050927733968009161390893 769097900238003435521585)
            ·
              refine ⟨576823425178502576641189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769097900238003435521585 576823425178502576641189)
              ·
                refine ⟨108154392220969233120223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576823425178502576641189 108154392220969233120223)
                ·
                  rfl

theorem cell19_355438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_355438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355438 prefixEnd_355438 := by exact prefixLift 355438
  have htrace : WordTrace (prefixWord ++ tailWord_355438) baseStart_355438 baseEnd_355438 := by
    simpa [prefixWord, tailWord_355438, baseEnd_355438] using wordTrace_append hprefix tailTrace_355438
  have hstable : (prefixWord ++ tailWord_355438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355438).length < 2 ^ (prefixWord ++ tailWord_355438).sum := by decide
  have hdescent : baseEnd_355438 < baseStart_355438 := by decide
  rcases family_descends (prefixWord ++ tailWord_355438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355440 : List Nat := [2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_355440 : Nat := 118140960795 + 355440 * 2 ^ 59
def prefixEnd_355440 : Nat := 4983230072969 + 3 ^ 40 * 355440 * 2
def baseEnd_355440 : Nat := 108155000790633821075773

theorem tailTrace_355440 : CollatzResearch.WordTrace tailWord_355440 prefixEnd_355440 108155000790633821075773 := by
  unfold tailWord_355440
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481980916154529582095887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8642641221539372776127849 6481980916154529582095887)
  ·
    refine ⟨9722971374231794373143831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6481980916154529582095887 9722971374231794373143831)
    ·
      refine ⟨14584457061347691559715747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9722971374231794373143831 14584457061347691559715747)
      ·
        refine ⟨21876685592021537339573621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14584457061347691559715747 21876685592021537339573621)
        ·
          refine ⟨2050939274252019125585027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21876685592021537339573621 2050939274252019125585027)
          ·
            refine ⟨3076408911378028688377541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050939274252019125585027 3076408911378028688377541)
            ·
              refine ⟨576826670883380379070789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3076408911378028688377541 576826670883380379070789)
              ·
                refine ⟨108155000790633821075773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576826670883380379070789 108155000790633821075773)
                ·
                  rfl

theorem cell19_355440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_355440 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355440 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355440 prefixEnd_355440 := by exact prefixLift 355440
  have htrace : WordTrace (prefixWord ++ tailWord_355440) baseStart_355440 baseEnd_355440 := by
    simpa [prefixWord, tailWord_355440, baseEnd_355440] using wordTrace_append hprefix tailTrace_355440
  have hstable : (prefixWord ++ tailWord_355440).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355440).length < 2 ^ (prefixWord ++ tailWord_355440).sum := by decide
  have hdescent : baseEnd_355440 < baseStart_355440 := by decide
  rcases family_descends (prefixWord ++ tailWord_355440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355495 : List Nat := [1, 1, 6, 2, 1, 1, 3, 4]
def baseStart_355495 : Nat := 118140960795 + 355495 * 2 ^ 59
def prefixEnd_355495 : Nat := 4983230072969 + 3 ^ 40 * 355495 * 2
def baseEnd_355495 : Nat := 108171736456409989853401

theorem tailTrace_355495 : CollatzResearch.WordTrace tailWord_355495 prefixEnd_355495 108171736456409989853401 := by
  unfold tailWord_355495
  simp only [CollatzResearch.WordTrace]
  refine ⟨12965967847109803557443939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8643978564739869038295959 12965967847109803557443939)
  ·
    refine ⟨19448951770664705336165909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12965967847109803557443939 19448951770664705336165909)
    ·
      refine ⟨911669614249908062632777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19448951770664705336165909 911669614249908062632777)
      ·
        refine ⟨683752210687431046974583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 911669614249908062632777 683752210687431046974583)
        ·
          refine ⟨1025628316031146570461875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683752210687431046974583 1025628316031146570461875)
          ·
            refine ⟨1538442474046719855692813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025628316031146570461875 1538442474046719855692813)
            ·
              refine ⟨576915927767519945884805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1538442474046719855692813 576915927767519945884805)
              ·
                refine ⟨108171736456409989853401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576915927767519945884805 108171736456409989853401)
                ·
                  rfl

theorem cell19_355495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_355495 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355495 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355495 prefixEnd_355495 := by exact prefixLift 355495
  have htrace : WordTrace (prefixWord ++ tailWord_355495) baseStart_355495 baseEnd_355495 := by
    simpa [prefixWord, tailWord_355495, baseEnd_355495] using wordTrace_append hprefix tailTrace_355495
  have hstable : (prefixWord ++ tailWord_355495).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355495).length < 2 ^ (prefixWord ++ tailWord_355495).sum := by decide
  have hdescent : baseEnd_355495 < baseStart_355495 := by decide
  rcases family_descends (prefixWord ++ tailWord_355495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355571 : List Nat := [1, 1, 1, 2, 2, 7, 2, 3]
def baseStart_355571 : Nat := 118140960795 + 355571 * 2 ^ 59
def prefixEnd_355571 : Nat := 4983230072969 + 3 ^ 40 * 355571 * 2
def baseEnd_355571 : Nat := 108194862103664332164305

theorem tailTrace_355571 : CollatzResearch.WordTrace tailWord_355571 prefixEnd_355571 108194862103664332164305 := by
  unfold tailWord_355571
  simp only [CollatzResearch.WordTrace]
  refine ⟨12968739794834468537210567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8645826529889645691473711 12968739794834468537210567)
  ·
    refine ⟨19453109692251702805815851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12968739794834468537210567 19453109692251702805815851)
    ·
      refine ⟨29179664538377554208723777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19453109692251702805815851 29179664538377554208723777)
      ·
        refine ⟨21884748403783165656542833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29179664538377554208723777 21884748403783165656542833)
        ·
          refine ⟨16413561302837374242407125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21884748403783165656542833 16413561302837374242407125)
          ·
            refine ⟨384692843035250958806417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16413561302837374242407125 384692843035250958806417)
            ·
              refine ⟨288519632276438219104813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384692843035250958806417 288519632276438219104813)
              ·
                refine ⟨108194862103664332164305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288519632276438219104813 108194862103664332164305)
                ·
                  rfl

theorem cell19_355571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_355571 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355571 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355571 prefixEnd_355571 := by exact prefixLift 355571
  have htrace : WordTrace (prefixWord ++ tailWord_355571) baseStart_355571 baseEnd_355571 := by
    simpa [prefixWord, tailWord_355571, baseEnd_355571] using wordTrace_append hprefix tailTrace_355571
  have hstable : (prefixWord ++ tailWord_355571).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355571).length < 2 ^ (prefixWord ++ tailWord_355571).sum := by decide
  have hdescent : baseEnd_355571 < baseStart_355571 := by decide
  rcases family_descends (prefixWord ++ tailWord_355571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355575 : List Nat := [1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_355575 : Nat := 118140960795 + 355575 * 2 ^ 59
def prefixEnd_355575 : Nat := 4983230072969 + 3 ^ 40 * 355575 * 2
def baseEnd_355575 : Nat := 108196079242993508075405

theorem tailTrace_355575 : CollatzResearch.WordTrace tailWord_355575 prefixEnd_355575 108196079242993508075405 := by
  unfold tailWord_355575
  simp only [CollatzResearch.WordTrace]
  refine ⟨12968885686819977220356179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8645923791213318146904119 12968885686819977220356179)
  ·
    refine ⟨19453328530229965830534269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12968885686819977220356179 19453328530229965830534269)
    ·
      refine ⟨7294998198836237186450351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19453328530229965830534269 7294998198836237186450351)
      ·
        refine ⟨10942497298254355779675527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7294998198836237186450351 10942497298254355779675527)
        ·
          refine ⟨16413745947381533669513291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10942497298254355779675527 16413745947381533669513291)
          ·
            refine ⟨24620618921072300504269937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16413745947381533669513291 24620618921072300504269937)
            ·
              refine ⟨18465464190804225378202453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24620618921072300504269937 18465464190804225378202453)
              ·
                refine ⟨108196079242993508075405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18465464190804225378202453 108196079242993508075405)
                ·
                  rfl

theorem cell19_355575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_355575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355575 prefixEnd_355575 := by exact prefixLift 355575
  have htrace : WordTrace (prefixWord ++ tailWord_355575) baseStart_355575 baseEnd_355575 := by
    simpa [prefixWord, tailWord_355575, baseEnd_355575] using wordTrace_append hprefix tailTrace_355575
  have hstable : (prefixWord ++ tailWord_355575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355575).length < 2 ^ (prefixWord ++ tailWord_355575).sum := by decide
  have hdescent : baseEnd_355575 < baseStart_355575 := by decide
  rcases family_descends (prefixWord ++ tailWord_355575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355632 : List Nat := [2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_355632 : Nat := 118140960795 + 355632 * 2 ^ 59
def prefixEnd_355632 : Nat := 4983230072969 + 3 ^ 40 * 355632 * 2
def baseEnd_355632 : Nat := 108213423478434264808583

theorem tailTrace_355632 : CollatzResearch.WordTrace tailWord_355632 prefixEnd_355632 108213423478434264808583 := by
  unfold tailWord_355632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6485482323806737977590575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8647309765075650636787433 6485482323806737977590575)
  ·
    refine ⟨9728223485710106966385863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6485482323806737977590575 9728223485710106966385863)
    ·
      refine ⟨14592335228565160449578795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9728223485710106966385863 14592335228565160449578795)
      ·
        refine ⟨21888502842847740674368193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14592335228565160449578795 21888502842847740674368193)
        ·
          refine ⟨16416377132135805505776145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21888502842847740674368193 16416377132135805505776145)
          ·
            refine ⟨12312282849101854129332109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16416377132135805505776145 12312282849101854129332109)
            ·
              refine ⟨4617106068413195298499541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12312282849101854129332109 4617106068413195298499541)
              ·
                refine ⟨108213423478434264808583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4617106068413195298499541 108213423478434264808583)
                ·
                  rfl

theorem cell19_355632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_355632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355632 prefixEnd_355632 := by exact prefixLift 355632
  have htrace : WordTrace (prefixWord ++ tailWord_355632) baseStart_355632 baseEnd_355632 := by
    simpa [prefixWord, tailWord_355632, baseEnd_355632] using wordTrace_append hprefix tailTrace_355632
  have hstable : (prefixWord ++ tailWord_355632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355632).length < 2 ^ (prefixWord ++ tailWord_355632).sum := by decide
  have hdescent : baseEnd_355632 < baseStart_355632 := by decide
  rcases family_descends (prefixWord ++ tailWord_355632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355649 : List Nat := [1, 2, 5, 2, 1, 8]
def baseStart_355649 : Nat := 118140960795 + 355649 * 2 ^ 59
def prefixEnd_355649 : Nat := 4983230072969 + 3 ^ 40 * 355649 * 2
def baseEnd_355649 : Nat := 12024288480064806936751

theorem tailTrace_355649 : CollatzResearch.WordTrace tailWord_355649 prefixEnd_355649 12024288480064806936751 := by
  unfold tailWord_355649
  simp only [CollatzResearch.WordTrace]
  refine ⟨12971584688551887858550001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8647723125701258572366667 12971584688551887858550001)
  ·
    refine ⟨9728688516413915893912501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12971584688551887858550001 9728688516413915893912501)
    ·
      refine ⟨912064548413804615054297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9728688516413915893912501 912064548413804615054297)
      ·
        refine ⟨684048411310353461290723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912064548413804615054297 684048411310353461290723)
        ·
          refine ⟨1026072616965530191936085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684048411310353461290723 1026072616965530191936085)
          ·
            refine ⟨12024288480064806936751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1026072616965530191936085 12024288480064806936751)
            ·
              rfl

theorem cell19_355649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 8].length) (baseStart_355649 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355649 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355649 prefixEnd_355649 := by exact prefixLift 355649
  have htrace : WordTrace (prefixWord ++ tailWord_355649) baseStart_355649 baseEnd_355649 := by
    simpa [prefixWord, tailWord_355649, baseEnd_355649] using wordTrace_append hprefix tailTrace_355649
  have hstable : (prefixWord ++ tailWord_355649).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355649).length < 2 ^ (prefixWord ++ tailWord_355649).sum := by decide
  have hdescent : baseEnd_355649 < baseStart_355649 := by decide
  rcases family_descends (prefixWord ++ tailWord_355649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355708 : List Nat := [2, 2, 2, 1, 1, 1, 10]
def baseStart_355708 : Nat := 118140960795 + 355708 * 2 ^ 59
def prefixEnd_355708 : Nat := 4983230072969 + 3 ^ 40 * 355708 * 2
def baseEnd_355708 : Nat := 36078849708562869039829

theorem tailTrace_355708 : CollatzResearch.WordTrace tailWord_355708 prefixEnd_355708 36078849708562869039829 := by
  unfold tailWord_355708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486868297669070467473889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8649157730225427289965185 6486868297669070467473889)
  ·
    refine ⟨4865151223251802850605417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6486868297669070467473889 4865151223251802850605417)
    ·
      refine ⟨3648863417438852137954063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4865151223251802850605417 3648863417438852137954063)
      ·
        refine ⟨5473295126158278206931095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3648863417438852137954063 5473295126158278206931095)
        ·
          refine ⟨8209942689237417310396643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5473295126158278206931095 8209942689237417310396643)
          ·
            refine ⟨12314914033856125965594965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8209942689237417310396643 12314914033856125965594965)
            ·
              refine ⟨36078849708562869039829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12314914033856125965594965 36078849708562869039829)
              ·
                rfl

theorem cell19_355708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_355708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355708 prefixEnd_355708 := by exact prefixLift 355708
  have htrace : WordTrace (prefixWord ++ tailWord_355708) baseStart_355708 baseEnd_355708 := by
    simpa [prefixWord, tailWord_355708, baseEnd_355708] using wordTrace_append hprefix tailTrace_355708
  have hstable : (prefixWord ++ tailWord_355708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355708).length < 2 ^ (prefixWord ++ tailWord_355708).sum := by decide
  have hdescent : baseEnd_355708 < baseStart_355708 := by decide
  rcases family_descends (prefixWord ++ tailWord_355708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355780 : List Nat := [2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_355780 : Nat := 118140960795 + 355780 * 2 ^ 59
def prefixEnd_355780 : Nat := 4983230072969 + 3 ^ 40 * 355780 * 2
def baseEnd_355780 : Nat := 108258457633613773519291

theorem tailTrace_355780 : CollatzResearch.WordTrace tailWord_355780 prefixEnd_355780 108258457633613773519291 := by
  unfold tailWord_355780
  simp only [CollatzResearch.WordTrace]
  refine ⟨6488181325538648615784397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8650908434051531487712529 6488181325538648615784397)
  ·
    refine ⟨2433067997076993230919149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6488181325538648615784397 2433067997076993230919149)
    ·
      refine ⟨912400498903872461594681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2433067997076993230919149 912400498903872461594681)
      ·
        refine ⟨684300374177904346196011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912400498903872461594681 684300374177904346196011)
        ·
          refine ⟨1026450561266856519294017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684300374177904346196011 1026450561266856519294017)
          ·
            refine ⟨769837920950142389470513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1026450561266856519294017 769837920950142389470513)
            ·
              refine ⟨577378440712606792102885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769837920950142389470513 577378440712606792102885)
              ·
                refine ⟨108258457633613773519291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577378440712606792102885 108258457633613773519291)
                ·
                  rfl

theorem cell19_355780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_355780 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355780 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355780 prefixEnd_355780 := by exact prefixLift 355780
  have htrace : WordTrace (prefixWord ++ tailWord_355780) baseStart_355780 baseEnd_355780 := by
    simpa [prefixWord, tailWord_355780, baseEnd_355780] using wordTrace_append hprefix tailTrace_355780
  have hstable : (prefixWord ++ tailWord_355780).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355780).length < 2 ^ (prefixWord ++ tailWord_355780).sum := by decide
  have hdescent : baseEnd_355780 < baseStart_355780 := by decide
  rcases family_descends (prefixWord ++ tailWord_355780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355898 : List Nat := [3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_355898 : Nat := 118140960795 + 355898 * 2 ^ 59
def prefixEnd_355898 : Nat := 4983230072969 + 3 ^ 40 * 355898 * 2
def baseEnd_355898 : Nat := 108294363243824462896747

theorem tailTrace_355898 : CollatzResearch.WordTrace tailWord_355898 prefixEnd_355898 108294363243824462896747 := by
  unfold tailWord_355898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245166616162450846091087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8653777643099868922909565 3245166616162450846091087)
  ·
    refine ⟨4867749924243676269136631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3245166616162450846091087 4867749924243676269136631)
    ·
      refine ⟨7301624886365514403704947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4867749924243676269136631 7301624886365514403704947)
      ·
        refine ⟨10952437329548271605557421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7301624886365514403704947 10952437329548271605557421)
        ·
          refine ⟨4107163998580601852084033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10952437329548271605557421 4107163998580601852084033)
          ·
            refine ⟨3080372998935451389063025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4107163998580601852084033 3080372998935451389063025)
            ·
              refine ⟨2310279749201588541797269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3080372998935451389063025 2310279749201588541797269)
              ·
                refine ⟨108294363243824462896747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2310279749201588541797269 108294363243824462896747)
                ·
                  rfl

theorem cell19_355898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_355898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355898 prefixEnd_355898 := by exact prefixLift 355898
  have htrace : WordTrace (prefixWord ++ tailWord_355898) baseStart_355898 baseEnd_355898 := by
    simpa [prefixWord, tailWord_355898, baseEnd_355898] using wordTrace_append hprefix tailTrace_355898
  have hstable : (prefixWord ++ tailWord_355898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355898).length < 2 ^ (prefixWord ++ tailWord_355898).sum := by decide
  have hdescent : baseEnd_355898 < baseStart_355898 := by decide
  rcases family_descends (prefixWord ++ tailWord_355898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_355911 : List Nat := [1, 1, 4, 1, 6, 1, 2, 3]
def baseStart_355911 : Nat := 118140960795 + 355911 * 2 ^ 59
def prefixEnd_355911 : Nat := 4983230072969 + 3 ^ 40 * 355911 * 2
def baseEnd_355911 : Nat := 108298318946644284607823

theorem tailTrace_355911 : CollatzResearch.WordTrace tailWord_355911 prefixEnd_355911 108298318946644284607823 := by
  unfold tailWord_355911
  simp only [CollatzResearch.WordTrace]
  refine ⟨12981140613602706604587587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8654093742401804403058391 12981140613602706604587587)
  ·
    refine ⟨19471710920404059906881381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12981140613602706604587587 19471710920404059906881381)
    ·
      refine ⟨3650945797575761232540259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19471710920404059906881381 3650945797575761232540259)
      ·
        refine ⟨5476418696363641848810389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3650945797575761232540259 5476418696363641848810389)
        ·
          refine ⟨256707126392045711662987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5476418696363641848810389 256707126392045711662987)
          ·
            refine ⟨385060689588068567494481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256707126392045711662987 385060689588068567494481)
            ·
              refine ⟨288795517191051425620861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385060689588068567494481 288795517191051425620861)
              ·
                refine ⟨108298318946644284607823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288795517191051425620861 108298318946644284607823)
                ·
                  rfl

theorem cell19_355911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 3].length) (baseStart_355911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_355911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_355911 prefixEnd_355911 := by exact prefixLift 355911
  have htrace : WordTrace (prefixWord ++ tailWord_355911) baseStart_355911 baseEnd_355911 := by
    simpa [prefixWord, tailWord_355911, baseEnd_355911] using wordTrace_append hprefix tailTrace_355911
  have hstable : (prefixWord ++ tailWord_355911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_355911).length < 2 ^ (prefixWord ++ tailWord_355911).sum := by decide
  have hdescent : baseEnd_355911 < baseStart_355911 := by decide
  rcases family_descends (prefixWord ++ tailWord_355911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356029 : List Nat := [1, 4, 1, 2, 1, 2, 5, 3]
def baseStart_356029 : Nat := 118140960795 + 356029 * 2 ^ 59
def prefixEnd_356029 : Nat := 4983230072969 + 3 ^ 40 * 356029 * 2
def baseEnd_356029 : Nat := 108334224556854973985279

theorem tailTrace_356029 : CollatzResearch.WordTrace tailWord_356029 prefixEnd_356029 108334224556854973985279 := by
  unfold tailWord_356029
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985444427175212757383141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8656962951450141838255427 12985444427175212757383141)
  ·
    refine ⟨2434770830095352392009339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12985444427175212757383141 2434770830095352392009339)
    ·
      refine ⟨3652156245143028588014009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434770830095352392009339 3652156245143028588014009)
      ·
        refine ⟨2739117183857271441010507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3652156245143028588014009 2739117183857271441010507)
        ·
          refine ⟨4108675775785907161515761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739117183857271441010507 4108675775785907161515761)
          ·
            refine ⟨3081506831839430371136821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4108675775785907161515761 3081506831839430371136821)
            ·
              refine ⟨288891265484946597294077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3081506831839430371136821 288891265484946597294077)
              ·
                refine ⟨108334224556854973985279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288891265484946597294077 108334224556854973985279)
                ·
                  rfl

theorem cell19_356029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_356029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356029 prefixEnd_356029 := by exact prefixLift 356029
  have htrace : WordTrace (prefixWord ++ tailWord_356029) baseStart_356029 baseEnd_356029 := by
    simpa [prefixWord, tailWord_356029, baseEnd_356029] using wordTrace_append hprefix tailTrace_356029
  have hstable : (prefixWord ++ tailWord_356029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356029).length < 2 ^ (prefixWord ++ tailWord_356029).sum := by decide
  have hdescent : baseEnd_356029 < baseStart_356029 := by decide
  rcases family_descends (prefixWord ++ tailWord_356029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356069 : List Nat := [1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_356069 : Nat := 118140960795 + 356069 * 2 ^ 59
def prefixEnd_356069 : Nat := 4983230072969 + 3 ^ 40 * 356069 * 2
def baseEnd_356069 : Nat := 108346395950146733096281

theorem tailTrace_356069 : CollatzResearch.WordTrace tailWord_356069 prefixEnd_356069 108346395950146733096281 := by
  unfold tailWord_356069
  simp only [CollatzResearch.WordTrace]
  refine ⟨12986903347030299588839261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8657935564686866392559507 12986903347030299588839261)
  ·
    refine ⟨4870088755136362345814723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12986903347030299588839261 4870088755136362345814723)
    ·
      refine ⟨7305133132704543518722085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4870088755136362345814723 7305133132704543518722085)
      ·
        refine ⟨1369712462382101909760391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7305133132704543518722085 1369712462382101909760391)
        ·
          refine ⟨2054568693573152864640587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369712462382101909760391 2054568693573152864640587)
          ·
            refine ⟨3081853040359729296960881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054568693573152864640587 3081853040359729296960881)
            ·
              refine ⟨2311389780269796972720661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3081853040359729296960881 2311389780269796972720661)
              ·
                refine ⟨108346395950146733096281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2311389780269796972720661 108346395950146733096281)
                ·
                  rfl

theorem cell19_356069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_356069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356069 prefixEnd_356069 := by exact prefixLift 356069
  have htrace : WordTrace (prefixWord ++ tailWord_356069) baseStart_356069 baseEnd_356069 := by
    simpa [prefixWord, tailWord_356069, baseEnd_356069] using wordTrace_append hprefix tailTrace_356069
  have hstable : (prefixWord ++ tailWord_356069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356069).length < 2 ^ (prefixWord ++ tailWord_356069).sum := by decide
  have hdescent : baseEnd_356069 < baseStart_356069 := by decide
  rcases family_descends (prefixWord ++ tailWord_356069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356086 : List Nat := [5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_356086 : Nat := 118140960795 + 356086 * 2 ^ 59
def prefixEnd_356086 : Nat := 4983230072969 + 3 ^ 40 * 356086 * 2
def baseEnd_356086 : Nat := 108351568792295730718457

theorem tailTrace_356086 : CollatzResearch.WordTrace tailWord_356086 prefixEnd_356086 108351568792295730718457 := by
  unfold tailWord_356086
  simp only [CollatzResearch.WordTrace]
  refine ⟨811720211748044468263007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8658348925312474328138741 811720211748044468263007)
  ·
    refine ⟨1217580317622066702394511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 811720211748044468263007 1217580317622066702394511)
    ·
      refine ⟨1826370476433100053591767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1217580317622066702394511 1826370476433100053591767)
      ·
        refine ⟨2739555714649650080387651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826370476433100053591767 2739555714649650080387651)
        ·
          refine ⟨4109333571974475120581477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739555714649650080387651 4109333571974475120581477)
          ·
            refine ⟨770500044745214085109027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4109333571974475120581477 770500044745214085109027)
            ·
              refine ⟨1155750067117821127663541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770500044745214085109027 1155750067117821127663541)
              ·
                refine ⟨108351568792295730718457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1155750067117821127663541 108351568792295730718457)
                ·
                  rfl

theorem cell19_356086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_356086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356086 prefixEnd_356086 := by exact prefixLift 356086
  have htrace : WordTrace (prefixWord ++ tailWord_356086) baseStart_356086 baseEnd_356086 := by
    simpa [prefixWord, tailWord_356086, baseEnd_356086] using wordTrace_append hprefix tailTrace_356086
  have hstable : (prefixWord ++ tailWord_356086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356086).length < 2 ^ (prefixWord ++ tailWord_356086).sum := by decide
  have hdescent : baseEnd_356086 < baseStart_356086 := by decide
  rcases family_descends (prefixWord ++ tailWord_356086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356103 : List Nat := [1, 1, 4, 4, 3, 1, 5]
def baseStart_356103 : Nat := 118140960795 + 356103 * 2 ^ 59
def prefixEnd_356103 : Nat := 4983230072969 + 3 ^ 40 * 356103 * 2
def baseEnd_356103 : Nat := 36118913878148242780211

theorem tailTrace_356103 : CollatzResearch.WordTrace tailWord_356103 prefixEnd_356103 36118913878148242780211 := by
  unfold tailWord_356103
  simp only [CollatzResearch.WordTrace]
  refine ⟨12988143428907123395576963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8658762285938082263717975 12988143428907123395576963)
  ·
    refine ⟨19482215143360685093365445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12988143428907123395576963 19482215143360685093365445)
    ·
      refine ⟨3652915339380128455006021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19482215143360685093365445 3652915339380128455006021)
      ·
        refine ⟨684921626133774085313629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3652915339380128455006021 684921626133774085313629)
        ·
          refine ⟨256845609800165281992611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 684921626133774085313629 256845609800165281992611)
          ·
            refine ⟨385268414700247922988917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256845609800165281992611 385268414700247922988917)
            ·
              refine ⟨36118913878148242780211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 385268414700247922988917 36118913878148242780211)
              ·
                rfl

theorem cell19_356103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 5].length) (baseStart_356103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356103 prefixEnd_356103 := by exact prefixLift 356103
  have htrace : WordTrace (prefixWord ++ tailWord_356103) baseStart_356103 baseEnd_356103 := by
    simpa [prefixWord, tailWord_356103, baseEnd_356103] using wordTrace_append hprefix tailTrace_356103
  have hstable : (prefixWord ++ tailWord_356103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356103).length < 2 ^ (prefixWord ++ tailWord_356103).sum := by decide
  have hdescent : baseEnd_356103 < baseStart_356103 := by decide
  rcases family_descends (prefixWord ++ tailWord_356103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356145 : List Nat := [1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_356145 : Nat := 118140960795 + 356145 * 2 ^ 59
def prefixEnd_356145 : Nat := 4983230072969 + 3 ^ 40 * 356145 * 2
def baseEnd_356145 : Nat := 108369521597401075407185

theorem tailTrace_356145 : CollatzResearch.WordTrace tailWord_356145 prefixEnd_356145 108369521597401075407185 := by
  unfold tailWord_356145
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989675294754964568605889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8659783529836643045737259 12989675294754964568605889)
  ·
    refine ⟨9742256471066223426454417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12989675294754964568605889 9742256471066223426454417)
    ·
      refine ⟨7306692353299667569840813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9742256471066223426454417 7306692353299667569840813)
      ·
        refine ⟨2740009632487375338690305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7306692353299667569840813 2740009632487375338690305)
        ·
          refine ⟨2055007224365531504017729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2740009632487375338690305 2055007224365531504017729)
          ·
            refine ⟨1541255418274148628013297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2055007224365531504017729 1541255418274148628013297)
            ·
              refine ⟨1155941563705611471009973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1541255418274148628013297 1155941563705611471009973)
              ·
                refine ⟨108369521597401075407185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1155941563705611471009973 108369521597401075407185)
                ·
                  rfl

theorem cell19_356145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_356145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356145 prefixEnd_356145 := by exact prefixLift 356145
  have htrace : WordTrace (prefixWord ++ tailWord_356145) baseStart_356145 baseEnd_356145 := by
    simpa [prefixWord, tailWord_356145, baseEnd_356145] using wordTrace_append hprefix tailTrace_356145
  have hstable : (prefixWord ++ tailWord_356145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356145).length < 2 ^ (prefixWord ++ tailWord_356145).sum := by decide
  have hdescent : baseEnd_356145 < baseStart_356145 := by decide
  rcases family_descends (prefixWord ++ tailWord_356145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356164 : List Nat := [2, 3, 4, 10]
def baseStart_356164 : Nat := 118140960795 + 356164 * 2 ^ 59
def prefixEnd_356164 : Nat := 4983230072969 + 3 ^ 40 * 356164 * 2
def baseEnd_356164 : Nat := 1337966703817464950431

theorem tailTrace_356164 : CollatzResearch.WordTrace tailWord_356164 prefixEnd_356164 1337966703817464950431 := by
  unfold tailWord_356164
  simp only [CollatzResearch.WordTrace]
  refine ⟨6495184140843065406773773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8660245521124087209031697 6495184140843065406773773)
  ·
    refine ⟨2435694052816149527540165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6495184140843065406773773 2435694052816149527540165)
    ·
      refine ⟨456692634903028036413781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2435694052816149527540165 456692634903028036413781)
      ·
        refine ⟨1337966703817464950431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 456692634903028036413781 1337966703817464950431)
        ·
          rfl

theorem cell19_356164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 10].length) (baseStart_356164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356164 prefixEnd_356164 := by exact prefixLift 356164
  have htrace : WordTrace (prefixWord ++ tailWord_356164) baseStart_356164 baseEnd_356164 := by
    simpa [prefixWord, tailWord_356164, baseEnd_356164] using wordTrace_append hprefix tailTrace_356164
  have hstable : (prefixWord ++ tailWord_356164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356164).length < 2 ^ (prefixWord ++ tailWord_356164).sum := by decide
  have hdescent : baseEnd_356164 < baseStart_356164 := by decide
  rcases family_descends (prefixWord ++ tailWord_356164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356181 : List Nat := [1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_356181 : Nat := 118140960795 + 356181 * 2 ^ 59
def prefixEnd_356181 : Nat := 4983230072969 + 3 ^ 40 * 356181 * 2
def baseEnd_356181 : Nat := 108380475851363658607087

theorem tailTrace_356181 : CollatzResearch.WordTrace tailWord_356181 prefixEnd_356181 108380475851363658607087 := by
  unfold tailWord_356181
  simp only [CollatzResearch.WordTrace]
  refine ⟨12990988322624542716916397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8660658881749695144610931 12990988322624542716916397)
  ·
    refine ⟨4871620620984203518843649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12990988322624542716916397 4871620620984203518843649)
    ·
      refine ⟨3653715465738152639132737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4871620620984203518843649 3653715465738152639132737)
      ·
        refine ⟨2740286599303614479349553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3653715465738152639132737 2740286599303614479349553)
        ·
          refine ⟨2055214949477710859512165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2740286599303614479349553 2055214949477710859512165)
          ·
            refine ⟨385352803027070786158531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2055214949477710859512165 385352803027070786158531)
            ·
              refine ⟨578029204540606179237797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385352803027070786158531 578029204540606179237797)
              ·
                refine ⟨108380475851363658607087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578029204540606179237797 108380475851363658607087)
                ·
                  rfl

theorem cell19_356181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_356181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356181 prefixEnd_356181 := by exact prefixLift 356181
  have htrace : WordTrace (prefixWord ++ tailWord_356181) baseStart_356181 baseEnd_356181 := by
    simpa [prefixWord, tailWord_356181, baseEnd_356181] using wordTrace_append hprefix tailTrace_356181
  have hstable : (prefixWord ++ tailWord_356181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356181).length < 2 ^ (prefixWord ++ tailWord_356181).sum := by decide
  have hdescent : baseEnd_356181 < baseStart_356181 := by decide
  rcases family_descends (prefixWord ++ tailWord_356181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356200 : List Nat := [2, 1, 4, 2, 1, 1, 5, 3]
def baseStart_356200 : Nat := 118140960795 + 356200 * 2 ^ 59
def prefixEnd_356200 : Nat := 4983230072969 + 3 ^ 40 * 356200 * 2
def baseEnd_356200 : Nat := 108386257263177244184813

theorem tailTrace_356200 : CollatzResearch.WordTrace tailWord_356200 prefixEnd_356200 108386257263177244184813 := by
  unfold tailWord_356200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6495840654777854480929027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8661120873037139307905369 6495840654777854480929027)
  ·
    refine ⟨9743760982166781721393541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6495840654777854480929027 9743760982166781721393541)
    ·
      refine ⟨1826955184156271572761289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9743760982166781721393541 1826955184156271572761289)
      ·
        refine ⟨1370216388117203679570967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1826955184156271572761289 1370216388117203679570967)
        ·
          refine ⟨2055324582175805519356451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1370216388117203679570967 2055324582175805519356451)
          ·
            refine ⟨3082986873263708279034677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2055324582175805519356451 3082986873263708279034677)
            ·
              refine ⟨289030019368472651159501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3082986873263708279034677 289030019368472651159501)
              ·
                refine ⟨108386257263177244184813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289030019368472651159501 108386257263177244184813)
                ·
                  rfl

theorem cell19_356200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_356200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356200 prefixEnd_356200 := by exact prefixLift 356200
  have htrace : WordTrace (prefixWord ++ tailWord_356200) baseStart_356200 baseEnd_356200 := by
    simpa [prefixWord, tailWord_356200, baseEnd_356200] using wordTrace_append hprefix tailTrace_356200
  have hstable : (prefixWord ++ tailWord_356200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356200).length < 2 ^ (prefixWord ++ tailWord_356200).sum := by decide
  have hdescent : baseEnd_356200 < baseStart_356200 := by decide
  rcases family_descends (prefixWord ++ tailWord_356200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356255 : List Nat := [1, 1, 2, 5, 3, 2, 2, 3]
def baseStart_356255 : Nat := 118140960795 + 356255 * 2 ^ 59
def prefixEnd_356255 : Nat := 4983230072969 + 3 ^ 40 * 356255 * 2
def baseEnd_356255 : Nat := 108402992928953412962441

theorem tailTrace_356255 : CollatzResearch.WordTrace tailWord_356255 prefixEnd_356255 108402992928953412962441 := by
  unfold tailWord_356255
  simp only [CollatzResearch.WordTrace]
  refine ⟨12993687324356453355110219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8662458216237635570073479 12993687324356453355110219)
  ·
    refine ⟨19490530986534680032665329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12993687324356453355110219 19490530986534680032665329)
    ·
      refine ⟨14617898239901010024498997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19490530986534680032665329 14617898239901010024498997)
      ·
        refine ⟨1370427959990719689796781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14617898239901010024498997 1370427959990719689796781)
        ·
          refine ⟨513910484996519883673793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1370427959990719689796781 513910484996519883673793)
          ·
            refine ⟨385432863747389912755345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513910484996519883673793 385432863747389912755345)
            ·
              refine ⟨289074647810542434566509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 385432863747389912755345 289074647810542434566509)
              ·
                refine ⟨108402992928953412962441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289074647810542434566509 108402992928953412962441)
                ·
                  rfl

theorem cell19_356255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_356255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356255 prefixEnd_356255 := by exact prefixLift 356255
  have htrace : WordTrace (prefixWord ++ tailWord_356255) baseStart_356255 baseEnd_356255 := by
    simpa [prefixWord, tailWord_356255, baseEnd_356255] using wordTrace_append hprefix tailTrace_356255
  have hstable : (prefixWord ++ tailWord_356255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356255).length < 2 ^ (prefixWord ++ tailWord_356255).sum := by decide
  have hdescent : baseEnd_356255 < baseStart_356255 := by decide
  rcases family_descends (prefixWord ++ tailWord_356255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356257 : List Nat := [1, 2, 3, 4, 2, 1, 1, 5]
def baseStart_356257 : Nat := 118140960795 + 356257 * 2 ^ 59
def prefixEnd_356257 : Nat := 4983230072969 + 3 ^ 40 * 356257 * 2
def baseEnd_356257 : Nat := 108403601498618000917991

theorem tailTrace_356257 : CollatzResearch.WordTrace tailWord_356257 prefixEnd_356257 108403601498618000917991 := by
  unfold tailWord_356257
  simp only [CollatzResearch.WordTrace]
  refine ⟨12993760270349207696683025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8662506846899471797788683 12993760270349207696683025)
  ·
    refine ⟨9745320202761905772512269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12993760270349207696683025 9745320202761905772512269)
    ·
      refine ⟨3654495076035714664692101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9745320202761905772512269 3654495076035714664692101)
      ·
        refine ⟨685217826756696499629769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3654495076035714664692101 685217826756696499629769)
        ·
          refine ⟨513913370067522374722327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685217826756696499629769 513913370067522374722327)
          ·
            refine ⟨770870055101283562083491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513913370067522374722327 770870055101283562083491)
            ·
              refine ⟨1156305082651925343125237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770870055101283562083491 1156305082651925343125237)
              ·
                refine ⟨108403601498618000917991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1156305082651925343125237 108403601498618000917991)
                ·
                  rfl

theorem cell19_356257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 5].length) (baseStart_356257 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356257 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356257 prefixEnd_356257 := by exact prefixLift 356257
  have htrace : WordTrace (prefixWord ++ tailWord_356257) baseStart_356257 baseEnd_356257 := by
    simpa [prefixWord, tailWord_356257, baseEnd_356257] using wordTrace_append hprefix tailTrace_356257
  have hstable : (prefixWord ++ tailWord_356257).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356257).length < 2 ^ (prefixWord ++ tailWord_356257).sum := by decide
  have hdescent : baseEnd_356257 < baseStart_356257 := by decide
  rcases family_descends (prefixWord ++ tailWord_356257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356270 : List Nat := [4, 1, 5, 1, 2, 1, 5]
def baseStart_356270 : Nat := 118140960795 + 356270 * 2 ^ 59
def prefixEnd_356270 : Nat := 4983230072969 + 3 ^ 40 * 356270 * 2
def baseEnd_356270 : Nat := 36135852400479274209689

theorem tailTrace_356270 : CollatzResearch.WordTrace tailWord_356270 prefixEnd_356270 36135852400479274209689 := by
  unfold tailWord_356270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624279302412763864613283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8662822946201407277937509 1624279302412763864613283)
  ·
    refine ⟨2436418953619145796919925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1624279302412763864613283 2436418953619145796919925)
    ·
      refine ⟨228414276901794918461243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2436418953619145796919925 228414276901794918461243)
      ·
        refine ⟨342621415352692377691865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228414276901794918461243 342621415352692377691865)
        ·
          refine ⟨256966061514519283268899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342621415352692377691865 256966061514519283268899)
          ·
            refine ⟨385449092271778924903349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256966061514519283268899 385449092271778924903349)
            ·
              refine ⟨36135852400479274209689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 385449092271778924903349 36135852400479274209689)
              ·
                rfl

theorem cell19_356270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 5].length) (baseStart_356270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356270 prefixEnd_356270 := by exact prefixLift 356270
  have htrace : WordTrace (prefixWord ++ tailWord_356270) baseStart_356270 baseEnd_356270 := by
    simpa [prefixWord, tailWord_356270, baseEnd_356270] using wordTrace_append hprefix tailTrace_356270
  have hstable : (prefixWord ++ tailWord_356270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356270).length < 2 ^ (prefixWord ++ tailWord_356270).sum := by decide
  have hdescent : baseEnd_356270 < baseStart_356270 := by decide
  rcases family_descends (prefixWord ++ tailWord_356270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356333 : List Nat := [1, 5, 1, 4, 1, 7]
def baseStart_356333 : Nat := 118140960795 + 356333 * 2 ^ 59
def prefixEnd_356333 : Nat := 4983230072969 + 3 ^ 40 * 356333 * 2
def baseEnd_356333 : Nat := 12047414127319149247655

theorem tailTrace_356333 : CollatzResearch.WordTrace tailWord_356333 prefixEnd_356333 12047414127319149247655 := by
  unfold tailWord_356333
  simp only [CollatzResearch.WordTrace]
  refine ⟨12996532218073872676449653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8664354812049248450966435 12996532218073872676449653)
  ·
    refine ⟨1218424895444425563417155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12996532218073872676449653 1218424895444425563417155)
    ·
      refine ⟨1827637343166638345125733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218424895444425563417155 1827637343166638345125733)
      ·
        refine ⟨342682001843744689711075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1827637343166638345125733 342682001843744689711075)
        ·
          refine ⟨514023002765617034566613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342682001843744689711075 514023002765617034566613)
          ·
            refine ⟨12047414127319149247655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 514023002765617034566613 12047414127319149247655)
            ·
              rfl

theorem cell19_356333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 7].length) (baseStart_356333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356333 prefixEnd_356333 := by exact prefixLift 356333
  have htrace : WordTrace (prefixWord ++ tailWord_356333) baseStart_356333 baseEnd_356333 := by
    simpa [prefixWord, tailWord_356333, baseEnd_356333] using wordTrace_append hprefix tailTrace_356333
  have hstable : (prefixWord ++ tailWord_356333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356333).length < 2 ^ (prefixWord ++ tailWord_356333).sum := by decide
  have hdescent : baseEnd_356333 < baseStart_356333 := by decide
  rcases family_descends (prefixWord ++ tailWord_356333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356337 : List Nat := [1, 2, 2, 2, 12]
def baseStart_356337 : Nat := 118140960795 + 356337 * 2 ^ 59
def prefixEnd_356337 : Nat := 4983230072969 + 3 ^ 40 * 356337 * 2
def baseEnd_356337 : Nat := 4015849788340797005185

theorem tailTrace_356337 : CollatzResearch.WordTrace tailWord_356337 prefixEnd_356337 4015849788340797005185 := by
  unfold tailWord_356337
  simp only [CollatzResearch.WordTrace]
  refine ⟨12996678110059381359595265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8664452073372920906396843 12996678110059381359595265)
  ·
    refine ⟨9747508582544536019696449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12996678110059381359595265 9747508582544536019696449)
    ·
      refine ⟨7310631436908402014772337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9747508582544536019696449 7310631436908402014772337)
      ·
        refine ⟨5482973577681301511079253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7310631436908402014772337 5482973577681301511079253)
        ·
          refine ⟨4015849788340797005185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5482973577681301511079253 4015849788340797005185)
          ·
            rfl

theorem cell19_356337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 12].length) (baseStart_356337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356337 prefixEnd_356337 := by exact prefixLift 356337
  have htrace : WordTrace (prefixWord ++ tailWord_356337) baseStart_356337 baseEnd_356337 := by
    simpa [prefixWord, tailWord_356337, baseEnd_356337] using wordTrace_append hprefix tailTrace_356337
  have hstable : (prefixWord ++ tailWord_356337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356337).length < 2 ^ (prefixWord ++ tailWord_356337).sum := by decide
  have hdescent : baseEnd_356337 < baseStart_356337 := by decide
  rcases family_descends (prefixWord ++ tailWord_356337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356350 : List Nat := [4, 2, 2, 2, 1, 3, 1, 4]
def baseStart_356350 : Nat := 118140960795 + 356350 * 2 ^ 59
def prefixEnd_356350 : Nat := 4983230072969 + 3 ^ 40 * 356350 * 2
def baseEnd_356350 : Nat := 108431899988021340851071

theorem tailTrace_356350 : CollatzResearch.WordTrace tailWord_356350 prefixEnd_356350 108431899988021340851071 := by
  unfold tailWord_356350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1624644032376535572477313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8664768172674856386545669 1624644032376535572477313)
  ·
    refine ⟨1218483024282401679357985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1624644032376535572477313 1218483024282401679357985)
    ·
      refine ⟨913862268211801259518489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1218483024282401679357985 913862268211801259518489)
      ·
        refine ⟨685396701158850944638867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 913862268211801259518489 685396701158850944638867)
        ·
          refine ⟨1028095051738276416958301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685396701158850944638867 1028095051738276416958301)
          ·
            refine ⟨385535644401853656359363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1028095051738276416958301 385535644401853656359363)
            ·
              refine ⟨578303466602780484539045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385535644401853656359363 578303466602780484539045)
              ·
                refine ⟨108431899988021340851071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578303466602780484539045 108431899988021340851071)
                ·
                  rfl

theorem cell19_356350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_356350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356350 prefixEnd_356350 := by exact prefixLift 356350
  have htrace : WordTrace (prefixWord ++ tailWord_356350) baseStart_356350 baseEnd_356350 := by
    simpa [prefixWord, tailWord_356350, baseEnd_356350] using wordTrace_append hprefix tailTrace_356350
  have hstable : (prefixWord ++ tailWord_356350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356350).length < 2 ^ (prefixWord ++ tailWord_356350).sum := by decide
  have hdescent : baseEnd_356350 < baseStart_356350 := by decide
  rcases family_descends (prefixWord ++ tailWord_356350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356365 : List Nat := [1, 7, 1, 2, 1, 1, 3, 3]
def baseStart_356365 : Nat := 118140960795 + 356365 * 2 ^ 59
def prefixEnd_356365 : Nat := 4983230072969 + 3 ^ 40 * 356365 * 2
def baseEnd_356365 : Nat := 108436464260505750517697

theorem tailTrace_356365 : CollatzResearch.WordTrace tailWord_356365 prefixEnd_356365 108436464260505750517697 := by
  unfold tailWord_356365
  simp only [CollatzResearch.WordTrace]
  refine ⟨12997699353957942141614549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8665132902638628094409699 12997699353957942141614549)
  ·
    refine ⟨304633578608389268944091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12997699353957942141614549 304633578608389268944091)
    ·
      refine ⟨456950367912583903416137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 304633578608389268944091 456950367912583903416137)
      ·
        refine ⟨342712775934437927562103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456950367912583903416137 342712775934437927562103)
        ·
          refine ⟨514069163901656891343155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342712775934437927562103 514069163901656891343155)
          ·
            refine ⟨771103745852485337014733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514069163901656891343155 771103745852485337014733)
            ·
              refine ⟨289163904694682001380525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 771103745852485337014733 289163904694682001380525)
              ·
                refine ⟨108436464260505750517697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289163904694682001380525 108436464260505750517697)
                ·
                  rfl

theorem cell19_356365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 3].length) (baseStart_356365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356365 prefixEnd_356365 := by exact prefixLift 356365
  have htrace : WordTrace (prefixWord ++ tailWord_356365) baseStart_356365 baseEnd_356365 := by
    simpa [prefixWord, tailWord_356365, baseEnd_356365] using wordTrace_append hprefix tailTrace_356365
  have hstable : (prefixWord ++ tailWord_356365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356365).length < 2 ^ (prefixWord ++ tailWord_356365).sum := by decide
  have hdescent : baseEnd_356365 < baseStart_356365 := by decide
  rcases family_descends (prefixWord ++ tailWord_356365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356430 : List Nat := [4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_356430 : Nat := 118140960795 + 356430 * 2 ^ 59
def prefixEnd_356430 : Nat := 4983230072969 + 3 ^ 40 * 356430 * 2
def baseEnd_356430 : Nat := 108456242774604859073075

theorem tailTrace_356430 : CollatzResearch.WordTrace tailWord_356430 prefixEnd_356430 108456242774604859073075 := by
  unfold tailWord_356430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625008762340307280341343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8666713399148305495153829 1625008762340307280341343)
  ·
    refine ⟨2437513143510460920512015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1625008762340307280341343 2437513143510460920512015)
    ·
      refine ⟨3656269715265691380768023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2437513143510460920512015 3656269715265691380768023)
      ·
        refine ⟨5484404572898537071152035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3656269715265691380768023 5484404572898537071152035)
        ·
          refine ⟨8226606859347805606728053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5484404572898537071152035 8226606859347805606728053)
          ·
            refine ⟨771244393063856775630755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8226606859347805606728053 771244393063856775630755)
            ·
              refine ⟨1156866589595785163446133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771244393063856775630755 1156866589595785163446133)
              ·
                refine ⟨108456242774604859073075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1156866589595785163446133 108456242774604859073075)
                ·
                  rfl

theorem cell19_356430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_356430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356430 prefixEnd_356430 := by exact prefixLift 356430
  have htrace : WordTrace (prefixWord ++ tailWord_356430) baseStart_356430 baseEnd_356430 := by
    simpa [prefixWord, tailWord_356430, baseEnd_356430] using wordTrace_append hprefix tailTrace_356430
  have hstable : (prefixWord ++ tailWord_356430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356430).length < 2 ^ (prefixWord ++ tailWord_356430).sum := by decide
  have hdescent : baseEnd_356430 < baseStart_356430 := by decide
  rcases family_descends (prefixWord ++ tailWord_356430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356451 : List Nat := [1, 1, 1, 5, 1, 1, 9]
def baseStart_356451 : Nat := 118140960795 + 356451 * 2 ^ 59
def prefixEnd_356451 : Nat := 4983230072969 + 3 ^ 40 * 356451 * 2
def baseEnd_356451 : Nat := 36154210918694344202117

theorem tailTrace_356451 : CollatzResearch.WordTrace tailWord_356451 prefixEnd_356451 36154210918694344202117 := by
  unfold tailWord_356451
  simp only [CollatzResearch.WordTrace]
  refine ⟨13000836031646378829245207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8667224021097585886163471 13000836031646378829245207)
  ·
    refine ⟨19501254047469568243867811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13000836031646378829245207 19501254047469568243867811)
    ·
      refine ⟨29251881071204352365801717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19501254047469568243867811 29251881071204352365801717)
      ·
        refine ⟨2742363850425408034293911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29251881071204352365801717 2742363850425408034293911)
        ·
          refine ⟨4113545775638112051440867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742363850425408034293911 4113545775638112051440867)
          ·
            refine ⟨6170318663457168077161301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113545775638112051440867 6170318663457168077161301)
            ·
              refine ⟨36154210918694344202117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6170318663457168077161301 36154210918694344202117)
              ·
                rfl

theorem cell19_356451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_356451 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356451 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356451 prefixEnd_356451 := by exact prefixLift 356451
  have htrace : WordTrace (prefixWord ++ tailWord_356451) baseStart_356451 baseEnd_356451 := by
    simpa [prefixWord, tailWord_356451, baseEnd_356451] using wordTrace_append hprefix tailTrace_356451
  have hstable : (prefixWord ++ tailWord_356451).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356451).length < 2 ^ (prefixWord ++ tailWord_356451).sum := by decide
  have hdescent : baseEnd_356451 < baseStart_356451 := by decide
  rcases family_descends (prefixWord ++ tailWord_356451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356489 : List Nat := [1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_356489 : Nat := 118140960795 + 356489 * 2 ^ 59
def prefixEnd_356489 : Nat := 4983230072969 + 3 ^ 40 * 356489 * 2
def baseEnd_356489 : Nat := 108474195579710203761803

theorem tailTrace_356489 : CollatzResearch.WordTrace tailWord_356489 prefixEnd_356489 108474195579710203761803 := by
  unfold tailWord_356489
  simp only [CollatzResearch.WordTrace]
  refine ⟨13002222005508711319128521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8668148003672474212752347 13002222005508711319128521)
  ·
    refine ⟨9751666504131533489346391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13002222005508711319128521 9751666504131533489346391)
    ·
      refine ⟨14627499756197300234019587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9751666504131533489346391 14627499756197300234019587)
      ·
        refine ⟨21941249634295950351029381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14627499756197300234019587 21941249634295950351029381)
        ·
          refine ⟨4113984306430490690818009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21941249634295950351029381 4113984306430490690818009)
          ·
            refine ⟨3085488229822868018113507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4113984306430490690818009 3085488229822868018113507)
            ·
              refine ⟨4628232344734302027170261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085488229822868018113507 4628232344734302027170261)
              ·
                refine ⟨108474195579710203761803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4628232344734302027170261 108474195579710203761803)
                ·
                  rfl

theorem cell19_356489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_356489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356489 prefixEnd_356489 := by exact prefixLift 356489
  have htrace : WordTrace (prefixWord ++ tailWord_356489) baseStart_356489 baseEnd_356489 := by
    simpa [prefixWord, tailWord_356489, baseEnd_356489] using wordTrace_append hprefix tailTrace_356489
  have hstable : (prefixWord ++ tailWord_356489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356489).length < 2 ^ (prefixWord ++ tailWord_356489).sum := by decide
  have hdescent : baseEnd_356489 < baseStart_356489 := by decide
  rcases family_descends (prefixWord ++ tailWord_356489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356506 : List Nat := [3, 1, 1, 5, 2, 7]
def baseStart_356506 : Nat := 118140960795 + 356506 * 2 ^ 59
def prefixEnd_356506 : Nat := 4983230072969 + 3 ^ 40 * 356506 * 2
def baseEnd_356506 : Nat := 12053263157984355709331

theorem tailTrace_356506 : CollatzResearch.WordTrace tailWord_356506 prefixEnd_356506 12053263157984355709331 := by
  unfold tailWord_356506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250710511611780805624343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8668561364298082148331581 3250710511611780805624343)
  ·
    refine ⟨4876065767417671208436515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3250710511611780805624343 4876065767417671208436515)
    ·
      refine ⟨7314098651126506812654773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4876065767417671208436515 7314098651126506812654773)
      ·
        refine ⟨685696748543110013686385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7314098651126506812654773 685696748543110013686385)
        ·
          refine ⟨514272561407332510264789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685696748543110013686385 514272561407332510264789)
          ·
            refine ⟨12053263157984355709331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 514272561407332510264789 12053263157984355709331)
            ·
              rfl

theorem cell19_356506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 7].length) (baseStart_356506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356506 prefixEnd_356506 := by exact prefixLift 356506
  have htrace : WordTrace (prefixWord ++ tailWord_356506) baseStart_356506 baseEnd_356506 := by
    simpa [prefixWord, tailWord_356506, baseEnd_356506] using wordTrace_append hprefix tailTrace_356506
  have hstable : (prefixWord ++ tailWord_356506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356506).length < 2 ^ (prefixWord ++ tailWord_356506).sum := by decide
  have hdescent : baseEnd_356506 < baseStart_356506 := by decide
  rcases family_descends (prefixWord ++ tailWord_356506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356637 : List Nat := [1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_356637 : Nat := 118140960795 + 356637 * 2 ^ 59
def prefixEnd_356637 : Nat := 4983230072969 + 3 ^ 40 * 356637 * 2
def baseEnd_356637 : Nat := 108519229734889712472511

theorem tailTrace_356637 : CollatzResearch.WordTrace tailWord_356637 prefixEnd_356637 108519229734889712472511 := by
  unfold tailWord_356637
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007620008972532595516165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8671746672648355063677443 13007620008972532595516165)
  ·
    refine ⟨2438928751682349861659281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13007620008972532595516165 2438928751682349861659281)
    ·
      refine ⟨1829196563761762396244461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2438928751682349861659281 1829196563761762396244461)
      ·
        refine ⟨685948711410660898591673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1829196563761762396244461 685948711410660898591673)
        ·
          refine ⟨514461533557995673943755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685948711410660898591673 514461533557995673943755)
          ·
            refine ⟨771692300336993510915633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514461533557995673943755 771692300336993510915633)
            ·
              refine ⟨578769225252745133186725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771692300336993510915633 578769225252745133186725)
              ·
                refine ⟨108519229734889712472511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578769225252745133186725 108519229734889712472511)
                ·
                  rfl

theorem cell19_356637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_356637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356637 prefixEnd_356637 := by exact prefixLift 356637
  have htrace : WordTrace (prefixWord ++ tailWord_356637) baseStart_356637 baseEnd_356637 := by
    simpa [prefixWord, tailWord_356637, baseEnd_356637] using wordTrace_append hprefix tailTrace_356637
  have hstable : (prefixWord ++ tailWord_356637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356637).length < 2 ^ (prefixWord ++ tailWord_356637).sum := by decide
  have hdescent : baseEnd_356637 < baseStart_356637 := by decide
  rcases family_descends (prefixWord ++ tailWord_356637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356639 : List Nat := [1, 1, 2, 4, 3, 2, 2, 4]
def baseStart_356639 : Nat := 118140960795 + 356639 * 2 ^ 59
def prefixEnd_356639 : Nat := 4983230072969 + 3 ^ 40 * 356639 * 2
def baseEnd_356639 : Nat := 108519838304554300428061

theorem tailTrace_356639 : CollatzResearch.WordTrace tailWord_356639 prefixEnd_356639 108519838304554300428061 := by
  unfold tailWord_356639
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007692954965286937088971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8671795303310191291392647 13007692954965286937088971)
  ·
    refine ⟨19511539432447930405633457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13007692954965286937088971 19511539432447930405633457)
    ·
      refine ⟨14633654574335947804225093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19511539432447930405633457 14633654574335947804225093)
      ·
        refine ⟨2743810232687990213292205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14633654574335947804225093 2743810232687990213292205)
        ·
          refine ⟨1028928837257996329984577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2743810232687990213292205 1028928837257996329984577)
          ·
            refine ⟨771696627943497247488433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028928837257996329984577 771696627943497247488433)
            ·
              refine ⟨578772470957622935616325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771696627943497247488433 578772470957622935616325)
              ·
                refine ⟨108519838304554300428061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 578772470957622935616325 108519838304554300428061)
                ·
                  rfl

theorem cell19_356639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_356639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356639 prefixEnd_356639 := by exact prefixLift 356639
  have htrace : WordTrace (prefixWord ++ tailWord_356639) baseStart_356639 baseEnd_356639 := by
    simpa [prefixWord, tailWord_356639, baseEnd_356639] using wordTrace_append hprefix tailTrace_356639
  have hstable : (prefixWord ++ tailWord_356639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356639).length < 2 ^ (prefixWord ++ tailWord_356639).sum := by decide
  have hdescent : baseEnd_356639 < baseStart_356639 := by decide
  rcases family_descends (prefixWord ++ tailWord_356639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356641 : List Nat := [1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_356641 : Nat := 118140960795 + 356641 * 2 ^ 59
def prefixEnd_356641 : Nat := 4983230072969 + 3 ^ 40 * 356641 * 2
def baseEnd_356641 : Nat := 108520446874218888383611

theorem tailTrace_356641 : CollatzResearch.WordTrace tailWord_356641 prefixEnd_356641 108520446874218888383611 := by
  unfold tailWord_356641
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007765900958041278661777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8671843933972027519107851 13007765900958041278661777)
  ·
    refine ⟨9755824425718530958996333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13007765900958041278661777 9755824425718530958996333)
    ·
      refine ⟨3658434159644449109623625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9755824425718530958996333 3658434159644449109623625)
      ·
        refine ⟨2743825619733336832217719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3658434159644449109623625 2743825619733336832217719)
        ·
          refine ⟨4115738429600005248326579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743825619733336832217719 4115738429600005248326579)
          ·
            refine ⟨6173607644400007872489869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115738429600005248326579 6173607644400007872489869)
            ·
              refine ⟨2315102866650002952183701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6173607644400007872489869 2315102866650002952183701)
              ·
                refine ⟨108520446874218888383611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2315102866650002952183701 108520446874218888383611)
                ·
                  rfl

theorem cell19_356641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_356641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356641 prefixEnd_356641 := by exact prefixLift 356641
  have htrace : WordTrace (prefixWord ++ tailWord_356641) baseStart_356641 baseEnd_356641 := by
    simpa [prefixWord, tailWord_356641, baseEnd_356641] using wordTrace_append hprefix tailTrace_356641
  have hstable : (prefixWord ++ tailWord_356641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356641).length < 2 ^ (prefixWord ++ tailWord_356641).sum := by decide
  have hdescent : baseEnd_356641 < baseStart_356641 := by decide
  rcases family_descends (prefixWord ++ tailWord_356641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356772 : List Nat := [2, 3, 1, 2, 1, 1, 6, 3]
def baseStart_356772 : Nat := 118140960795 + 356772 * 2 ^ 59
def prefixEnd_356772 : Nat := 4983230072969 + 3 ^ 40 * 356772 * 2
def baseEnd_356772 : Nat := 108560308187249399472143

theorem tailTrace_356772 : CollatzResearch.WordTrace tailWord_356772 prefixEnd_356772 108560308187249399472143 := by
  unfold tailWord_356772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6506271931741725325840285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8675029242322300434453713 6506271931741725325840285)
  ·
    refine ⟨2439851974403146997190107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6506271931741725325840285 2439851974403146997190107)
    ·
      refine ⟨3659777961604720495785161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2439851974403146997190107 3659777961604720495785161)
      ·
        refine ⟨2744833471203540371838871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3659777961604720495785161 2744833471203540371838871)
        ·
          refine ⟨4117250206805310557758307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2744833471203540371838871 4117250206805310557758307)
          ·
            refine ⟨6175875310207965836637461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117250206805310557758307 6175875310207965836637461)
            ·
              refine ⟨289494155165998398592381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6175875310207965836637461 289494155165998398592381)
              ·
                refine ⟨108560308187249399472143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289494155165998398592381 108560308187249399472143)
                ·
                  rfl

theorem cell19_356772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_356772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356772 prefixEnd_356772 := by exact prefixLift 356772
  have htrace : WordTrace (prefixWord ++ tailWord_356772) baseStart_356772 baseEnd_356772 := by
    simpa [prefixWord, tailWord_356772, baseEnd_356772] using wordTrace_append hprefix tailTrace_356772
  have hstable : (prefixWord ++ tailWord_356772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356772).length < 2 ^ (prefixWord ++ tailWord_356772).sum := by decide
  have hdescent : baseEnd_356772 < baseStart_356772 := by decide
  rcases family_descends (prefixWord ++ tailWord_356772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356789 : List Nat := [1, 3, 3, 2, 4, 1, 5]
def baseStart_356789 : Nat := 118140960795 + 356789 * 2 ^ 59
def prefixEnd_356789 : Nat := 4983230072969 + 3 ^ 40 * 356789 * 2
def baseEnd_356789 : Nat := 36188493676466132364773

theorem tailTrace_356789 : CollatzResearch.WordTrace tailWord_356789 prefixEnd_356789 36188493676466132364773 := by
  unfold tailWord_356789
  simp only [CollatzResearch.WordTrace]
  refine ⟨13013163904421862555049421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8675442602947908370032947 13013163904421862555049421)
  ·
    refine ⟨4879936464158198458143533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13013163904421862555049421 4879936464158198458143533)
    ·
      refine ⟨1829976174059324421803825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4879936464158198458143533 1829976174059324421803825)
      ·
        refine ⟨1372482130544493316352869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1829976174059324421803825 1372482130544493316352869)
        ·
          refine ⟨257340399477092496816163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1372482130544493316352869 257340399477092496816163)
          ·
            refine ⟨386010599215638745224245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257340399477092496816163 386010599215638745224245)
            ·
              refine ⟨36188493676466132364773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 386010599215638745224245 36188493676466132364773)
              ·
                rfl

theorem cell19_356789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 5].length) (baseStart_356789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356789 prefixEnd_356789 := by exact prefixLift 356789
  have htrace : WordTrace (prefixWord ++ tailWord_356789) baseStart_356789 baseEnd_356789 := by
    simpa [prefixWord, tailWord_356789, baseEnd_356789] using wordTrace_append hprefix tailTrace_356789
  have hstable : (prefixWord ++ tailWord_356789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356789).length < 2 ^ (prefixWord ++ tailWord_356789).sum := by decide
  have hdescent : baseEnd_356789 < baseStart_356789 := by decide
  rcases family_descends (prefixWord ++ tailWord_356789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356793 : List Nat := [1, 2, 1, 4, 3, 1, 7]
def baseStart_356793 : Nat := 118140960795 + 356793 * 2 ^ 59
def prefixEnd_356793 : Nat := 4983230072969 + 3 ^ 40 * 356793 * 2
def baseEnd_356793 : Nat := 36188899389575857668473

theorem tailTrace_356793 : CollatzResearch.WordTrace tailWord_356793 prefixEnd_356793 36188899389575857668473 := by
  unfold tailWord_356793
  simp only [CollatzResearch.WordTrace]
  refine ⟨13013309796407371238195033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8675539864271580825463355 13013309796407371238195033)
  ·
    refine ⟨9759982347305528428646275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13013309796407371238195033 9759982347305528428646275)
    ·
      refine ⟨14639973520958292642969413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9759982347305528428646275 14639973520958292642969413)
      ·
        refine ⟨2744995035179679870556765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14639973520958292642969413 2744995035179679870556765)
        ·
          refine ⟨1029373138192379951458787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2744995035179679870556765 1029373138192379951458787)
          ·
            refine ⟨1544059707288569927188181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029373138192379951458787 1544059707288569927188181)
            ·
              refine ⟨36188899389575857668473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1544059707288569927188181 36188899389575857668473)
              ·
                rfl

theorem cell19_356793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_356793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356793 prefixEnd_356793 := by exact prefixLift 356793
  have htrace : WordTrace (prefixWord ++ tailWord_356793) baseStart_356793 baseEnd_356793 := by
    simpa [prefixWord, tailWord_356793, baseEnd_356793] using wordTrace_append hprefix tailTrace_356793
  have hstable : (prefixWord ++ tailWord_356793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356793).length < 2 ^ (prefixWord ++ tailWord_356793).sum := by decide
  have hdescent : baseEnd_356793 < baseStart_356793 := by decide
  rcases family_descends (prefixWord ++ tailWord_356793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356831 : List Nat := [1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_356831 : Nat := 118140960795 + 356831 * 2 ^ 59
def prefixEnd_356831 : Nat := 4983230072969 + 3 ^ 40 * 356831 * 2
def baseEnd_356831 : Nat := 108578260992354744160871

theorem tailTrace_356831 : CollatzResearch.WordTrace tailWord_356831 prefixEnd_356831 108578260992354744160871 := by
  unfold tailWord_356831
  simp only [CollatzResearch.WordTrace]
  refine ⟨13014695770269703728078347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8676463846846469152052231 13014695770269703728078347)
  ·
    refine ⟨19522043655404555592117521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13014695770269703728078347 19522043655404555592117521)
    ·
      refine ⟨14641532741553416694088141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19522043655404555592117521 14641532741553416694088141)
      ·
        refine ⟨5490574778082531260283053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14641532741553416694088141 5490574778082531260283053)
        ·
          refine ⟨2058965541780949222606145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5490574778082531260283053 2058965541780949222606145)
          ·
            refine ⟨1544224156335711916954609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2058965541780949222606145 1544224156335711916954609)
            ·
              refine ⟨1158168117251783937715957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1544224156335711916954609 1158168117251783937715957)
              ·
                refine ⟨108578260992354744160871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1158168117251783937715957 108578260992354744160871)
                ·
                  rfl

theorem cell19_356831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_356831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356831 prefixEnd_356831 := by exact prefixLift 356831
  have htrace : WordTrace (prefixWord ++ tailWord_356831) baseStart_356831 baseEnd_356831 := by
    simpa [prefixWord, tailWord_356831, baseEnd_356831] using wordTrace_append hprefix tailTrace_356831
  have hstable : (prefixWord ++ tailWord_356831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356831).length < 2 ^ (prefixWord ++ tailWord_356831).sum := by decide
  have hdescent : baseEnd_356831 < baseStart_356831 := by decide
  rcases family_descends (prefixWord ++ tailWord_356831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356850 : List Nat := [3, 2, 1, 4, 9]
def baseStart_356850 : Nat := 118140960795 + 356850 * 2 ^ 59
def prefixEnd_356850 : Nat := 4983230072969 + 3 ^ 40 * 356850 * 2
def baseEnd_356850 : Nat := 4021631200154382582911

theorem tailTrace_356850 : CollatzResearch.WordTrace tailWord_356850 prefixEnd_356850 4021631200154382582911 := by
  unfold tailWord_356850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3253847189300217493255001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8676925838133913315346669 3253847189300217493255001)
  ·
    refine ⟨2440385391975163119941251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3253847189300217493255001 2440385391975163119941251)
    ·
      refine ⟨3660578087962744679911877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2440385391975163119941251 3660578087962744679911877)
      ·
        refine ⟨686358391493014627483477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3660578087962744679911877 686358391493014627483477)
        ·
          refine ⟨4021631200154382582911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 686358391493014627483477 4021631200154382582911)
          ·
            rfl

theorem cell19_356850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 9].length) (baseStart_356850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356850 prefixEnd_356850 := by exact prefixLift 356850
  have htrace : WordTrace (prefixWord ++ tailWord_356850) baseStart_356850 baseEnd_356850 := by
    simpa [prefixWord, tailWord_356850, baseEnd_356850] using wordTrace_append hprefix tailTrace_356850
  have hstable : (prefixWord ++ tailWord_356850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356850).length < 2 ^ (prefixWord ++ tailWord_356850).sum := by decide
  have hdescent : baseEnd_356850 < baseStart_356850 := by decide
  rcases family_descends (prefixWord ++ tailWord_356850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356869 : List Nat := [1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_356869 : Nat := 118140960795 + 356869 * 2 ^ 59
def prefixEnd_356869 : Nat := 4983230072969 + 3 ^ 40 * 356869 * 2
def baseEnd_356869 : Nat := 108589823815981915316323

theorem tailTrace_356869 : CollatzResearch.WordTrace tailWord_356869 prefixEnd_356869 108589823815981915316323 := by
  unfold tailWord_356869
  simp only [CollatzResearch.WordTrace]
  refine ⟨13016081744132036217961661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8677387829421357478641107 13016081744132036217961661)
  ·
    refine ⟨4881030654049513581735623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13016081744132036217961661 4881030654049513581735623)
    ·
      refine ⟨7321545981074270372603435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4881030654049513581735623 7321545981074270372603435)
      ·
        refine ⟨10982318971611405558905153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7321545981074270372603435 10982318971611405558905153)
        ·
          refine ⟨8236739228708554169178865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10982318971611405558905153 8236739228708554169178865)
          ·
            refine ⟨6177554421531415626884149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8236739228708554169178865 6177554421531415626884149)
            ·
              refine ⟨579145727018570215020389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6177554421531415626884149 579145727018570215020389)
              ·
                refine ⟨108589823815981915316323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 579145727018570215020389 108589823815981915316323)
                ·
                  rfl

theorem cell19_356869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_356869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356869 prefixEnd_356869 := by exact prefixLift 356869
  have htrace : WordTrace (prefixWord ++ tailWord_356869) baseStart_356869 baseEnd_356869 := by
    simpa [prefixWord, tailWord_356869, baseEnd_356869] using wordTrace_append hprefix tailTrace_356869
  have hstable : (prefixWord ++ tailWord_356869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356869).length < 2 ^ (prefixWord ++ tailWord_356869).sum := by decide
  have hdescent : baseEnd_356869 < baseStart_356869 := by decide
  rcases family_descends (prefixWord ++ tailWord_356869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356903 : List Nat := [1, 1, 7, 2, 1, 1, 6]
def baseStart_356903 : Nat := 118140960795 + 356903 * 2 ^ 59
def prefixEnd_356903 : Nat := 4983230072969 + 3 ^ 40 * 356903 * 2
def baseEnd_356903 : Nat := 36200056500093303520225

theorem tailTrace_356903 : CollatzResearch.WordTrace tailWord_356903 prefixEnd_356903 36200056500093303520225 := by
  unfold tailWord_356903
  simp only [CollatzResearch.WordTrace]
  refine ⟨13017321826008860024699363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8678214550672573349799575 13017321826008860024699363)
  ·
    refine ⟨19525982739013290037049045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13017321826008860024699363 19525982739013290037049045)
    ·
      refine ⟨457640220445623985243337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19525982739013290037049045 457640220445623985243337)
      ·
        refine ⟨343230165334217988932503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457640220445623985243337 343230165334217988932503)
        ·
          refine ⟨514845248001326983398755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343230165334217988932503 514845248001326983398755)
          ·
            refine ⟨772267872001990475098133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514845248001326983398755 772267872001990475098133)
            ·
              refine ⟨36200056500093303520225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 772267872001990475098133 36200056500093303520225)
              ·
                rfl

theorem cell19_356903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 6].length) (baseStart_356903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356903 prefixEnd_356903 := by exact prefixLift 356903
  have htrace : WordTrace (prefixWord ++ tailWord_356903) baseStart_356903 baseEnd_356903 := by
    simpa [prefixWord, tailWord_356903, baseEnd_356903] using wordTrace_append hprefix tailTrace_356903
  have hstable : (prefixWord ++ tailWord_356903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356903).length < 2 ^ (prefixWord ++ tailWord_356903).sum := by decide
  have hdescent : baseEnd_356903 < baseStart_356903 := by decide
  rcases family_descends (prefixWord ++ tailWord_356903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356941 : List Nat := [1, 6, 1, 1, 2, 1, 4, 3]
def baseStart_356941 : Nat := 118140960795 + 356941 * 2 ^ 59
def prefixEnd_356941 : Nat := 4983230072969 + 3 ^ 40 * 356941 * 2
def baseEnd_356941 : Nat := 108611732323907081716127

theorem tailTrace_356941 : CollatzResearch.WordTrace tailWord_356941 prefixEnd_356941 108611732323907081716127 := by
  unfold tailWord_356941
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018707799871192514582677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8679138533247461676388451 13018707799871192514582677)
  ·
    refine ⟨610251928118962149121063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13018707799871192514582677 610251928118962149121063)
    ·
      refine ⟨915377892178443223681595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610251928118962149121063 915377892178443223681595)
      ·
        refine ⟨1373066838267664835522393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915377892178443223681595 1373066838267664835522393)
        ·
          refine ⟨1029800128700748626641795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1373066838267664835522393 1029800128700748626641795)
          ·
            refine ⟨1544700193051122939962693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029800128700748626641795 1544700193051122939962693)
            ·
              refine ⟨289631286197085551243005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1544700193051122939962693 289631286197085551243005)
              ·
                refine ⟨108611732323907081716127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289631286197085551243005 108611732323907081716127)
                ·
                  rfl

theorem cell19_356941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_356941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356941 prefixEnd_356941 := by exact prefixLift 356941
  have htrace : WordTrace (prefixWord ++ tailWord_356941) baseStart_356941 baseEnd_356941 := by
    simpa [prefixWord, tailWord_356941, baseEnd_356941] using wordTrace_append hprefix tailTrace_356941
  have hstable : (prefixWord ++ tailWord_356941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356941).length < 2 ^ (prefixWord ++ tailWord_356941).sum := by decide
  have hdescent : baseEnd_356941 < baseStart_356941 := by decide
  rcases family_descends (prefixWord ++ tailWord_356941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_356945 : List Nat := [1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_356945 : Nat := 118140960795 + 356945 * 2 ^ 59
def prefixEnd_356945 : Nat := 4983230072969 + 3 ^ 40 * 356945 * 2
def baseEnd_356945 : Nat := 108612949463236257627227

theorem tailTrace_356945 : CollatzResearch.WordTrace tailWord_356945 prefixEnd_356945 108612949463236257627227 := by
  unfold tailWord_356945
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018853691856701197728289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8679235794571134131818859 13018853691856701197728289)
  ·
    refine ⟨9764140268892525898296217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13018853691856701197728289 9764140268892525898296217)
    ·
      refine ⟨7323105201669394423722163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9764140268892525898296217 7323105201669394423722163)
      ·
        refine ⟨10984657802504091635583245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7323105201669394423722163 10984657802504091635583245)
        ·
          refine ⟨4119246675939034363343717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10984657802504091635583245 4119246675939034363343717)
          ·
            refine ⟨772358751738568943126947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4119246675939034363343717 772358751738568943126947)
            ·
              refine ⟨1158538127607853414690421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772358751738568943126947 1158538127607853414690421)
              ·
                refine ⟨108612949463236257627227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1158538127607853414690421 108612949463236257627227)
                ·
                  rfl

theorem cell19_356945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_356945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_356945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_356945 prefixEnd_356945 := by exact prefixLift 356945
  have htrace : WordTrace (prefixWord ++ tailWord_356945) baseStart_356945 baseEnd_356945 := by
    simpa [prefixWord, tailWord_356945, baseEnd_356945] using wordTrace_append hprefix tailTrace_356945
  have hstable : (prefixWord ++ tailWord_356945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_356945).length < 2 ^ (prefixWord ++ tailWord_356945).sum := by decide
  have hdescent : baseEnd_356945 < baseStart_356945 := by decide
  rcases family_descends (prefixWord ++ tailWord_356945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357023 : List Nat := [1, 1, 2, 15]
def baseStart_357023 : Nat := 118140960795 + 357023 * 2 ^ 59
def prefixEnd_357023 : Nat := 4983230072969 + 3 ^ 40 * 357023 * 2
def baseEnd_357023 : Nat := 1341193625680928245601

theorem tailTrace_357023 : CollatzResearch.WordTrace tailWord_357023 prefixEnd_357023 1341193625680928245601 := by
  unfold tailWord_357023
  simp only [CollatzResearch.WordTrace]
  refine ⟨13021698585574120519067723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8681132390382747012711815 13021698585574120519067723)
  ·
    refine ⟨19532547878361180778601585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13021698585574120519067723 19532547878361180778601585)
    ·
      refine ⟨14649410908770885583951189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19532547878361180778601585 14649410908770885583951189)
      ·
        refine ⟨1341193625680928245601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 14649410908770885583951189 1341193625680928245601)
        ·
          rfl

theorem cell19_357023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 15].length) (baseStart_357023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357023 prefixEnd_357023 := by exact prefixLift 357023
  have htrace : WordTrace (prefixWord ++ tailWord_357023) baseStart_357023 baseEnd_357023 := by
    simpa [prefixWord, tailWord_357023, baseEnd_357023] using wordTrace_append hprefix tailTrace_357023
  have hstable : (prefixWord ++ tailWord_357023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357023).length < 2 ^ (prefixWord ++ tailWord_357023).sum := by decide
  have hdescent : baseEnd_357023 < baseStart_357023 := by decide
  rcases family_descends (prefixWord ++ tailWord_357023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357034 : List Nat := [3, 1, 5, 2, 1, 2, 1, 4]
def baseStart_357034 : Nat := 118140960795 + 357034 * 2 ^ 59
def prefixEnd_357034 : Nat := 4983230072969 + 3 ^ 40 * 357034 * 2
def baseEnd_357034 : Nat := 108640030813310421649207

theorem tailTrace_357034 : CollatzResearch.WordTrace tailWord_357034 prefixEnd_357034 108640030813310421649207 := by
  unfold tailWord_357034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3255524947133567349429539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8681399859022846265145437 3255524947133567349429539)
  ·
    refine ⟨4883287420700351024144309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3255524947133567349429539 4883287420700351024144309)
    ·
      refine ⟨457808195690657908513529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4883287420700351024144309 457808195690657908513529)
      ·
        refine ⟨343356146767993431385147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457808195690657908513529 343356146767993431385147)
        ·
          refine ⟨515034220151990147077721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343356146767993431385147 515034220151990147077721)
          ·
            refine ⟨386275665113992610308291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515034220151990147077721 386275665113992610308291)
            ·
              refine ⟨579413497670988915462437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386275665113992610308291 579413497670988915462437)
              ·
                refine ⟨108640030813310421649207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 579413497670988915462437 108640030813310421649207)
                ·
                  rfl

theorem cell19_357034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_357034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357034 prefixEnd_357034 := by exact prefixLift 357034
  have htrace : WordTrace (prefixWord ++ tailWord_357034) baseStart_357034 baseEnd_357034 := by
    simpa [prefixWord, tailWord_357034, baseEnd_357034] using wordTrace_append hprefix tailTrace_357034
  have hstable : (prefixWord ++ tailWord_357034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357034).length < 2 ^ (prefixWord ++ tailWord_357034).sum := by decide
  have hdescent : baseEnd_357034 < baseStart_357034 := by decide
  rcases family_descends (prefixWord ++ tailWord_357034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357076 : List Nat := [2, 4, 1, 3, 2, 1, 6]
def baseStart_357076 : Nat := 118140960795 + 357076 * 2 ^ 59
def prefixEnd_357076 : Nat := 4983230072969 + 3 ^ 40 * 357076 * 2
def baseEnd_357076 : Nat := 36217603592088922905253

theorem tailTrace_357076 : CollatzResearch.WordTrace tailWord_357076 prefixEnd_357076 36217603592088922905253 := by
  unfold tailWord_357076
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511815827191055285373541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8682421102921407047164721 6511815827191055285373541)
  ·
    refine ⟨1220965467598322866007539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6511815827191055285373541 1220965467598322866007539)
    ·
      refine ⟨1831448201397484299011309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1220965467598322866007539 1831448201397484299011309)
      ·
        refine ⟨686793075524056612129241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1831448201397484299011309 686793075524056612129241)
        ·
          refine ⟨515094806643042459096931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686793075524056612129241 515094806643042459096931)
          ·
            refine ⟨772642209964563688645397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515094806643042459096931 772642209964563688645397)
            ·
              refine ⟨36217603592088922905253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 772642209964563688645397 36217603592088922905253)
              ·
                rfl

theorem cell19_357076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_357076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357076 prefixEnd_357076 := by exact prefixLift 357076
  have htrace : WordTrace (prefixWord ++ tailWord_357076) baseStart_357076 baseEnd_357076 := by
    simpa [prefixWord, tailWord_357076, baseEnd_357076] using wordTrace_append hprefix tailTrace_357076
  have hstable : (prefixWord ++ tailWord_357076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357076).length < 2 ^ (prefixWord ++ tailWord_357076).sum := by decide
  have hdescent : baseEnd_357076 < baseStart_357076 := by decide
  rcases family_descends (prefixWord ++ tailWord_357076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357099 : List Nat := [1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_357099 : Nat := 118140960795 + 357099 * 2 ^ 59
def prefixEnd_357099 : Nat := 4983230072969 + 3 ^ 40 * 357099 * 2
def baseEnd_357099 : Nat := 108659809327409530204585

theorem tailTrace_357099 : CollatzResearch.WordTrace tailWord_357099 prefixEnd_357099 108659809327409530204585 := by
  unfold tailWord_357099
  simp only [CollatzResearch.WordTrace]
  refine ⟨13024470533298785498834351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8682980355532523665889567 13024470533298785498834351)
  ·
    refine ⟨19536705799948178248251527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13024470533298785498834351 19536705799948178248251527)
    ·
      refine ⟨29305058699922267372377291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19536705799948178248251527 29305058699922267372377291)
      ·
        refine ⟨43957588049883401058565937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29305058699922267372377291 43957588049883401058565937)
        ·
          refine ⟨32968191037412550793924453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43957588049883401058565937 32968191037412550793924453)
          ·
            refine ⟨6181535819514853273860835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32968191037412550793924453 6181535819514853273860835)
            ·
              refine ⟨9272303729272279910791253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6181535819514853273860835 9272303729272279910791253)
              ·
                refine ⟨108659809327409530204585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9272303729272279910791253 108659809327409530204585)
                ·
                  rfl

theorem cell19_357099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_357099 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357099 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357099 prefixEnd_357099 := by exact prefixLift 357099
  have htrace : WordTrace (prefixWord ++ tailWord_357099) baseStart_357099 baseEnd_357099 := by
    simpa [prefixWord, tailWord_357099, baseEnd_357099] using wordTrace_append hprefix tailTrace_357099
  have hstable : (prefixWord ++ tailWord_357099).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357099).length < 2 ^ (prefixWord ++ tailWord_357099).sum := by decide
  have hdescent : baseEnd_357099 < baseStart_357099 := by decide
  rcases family_descends (prefixWord ++ tailWord_357099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357108 : List Nat := [2, 6, 1, 1, 2, 2, 2, 3]
def baseStart_357108 : Nat := 118140960795 + 357108 * 2 ^ 59
def prefixEnd_357108 : Nat := 4983230072969 + 3 ^ 40 * 357108 * 2
def baseEnd_357108 : Nat := 108662547890900176004561

theorem tailTrace_357108 : CollatzResearch.WordTrace tailWord_357108 prefixEnd_357108 108662547890900176004561 := by
  unfold tailWord_357108
  simp only [CollatzResearch.WordTrace]
  refine ⟨6512399395133090017955989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8683199193510786690607985 6512399395133090017955989)
  ·
    refine ⟨305268721646863594591687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6512399395133090017955989 305268721646863594591687)
    ·
      refine ⟨457903082470295391887531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305268721646863594591687 457903082470295391887531)
      ·
        refine ⟨686854623705443087831297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457903082470295391887531 686854623705443087831297)
        ·
          refine ⟨515140967779082315873473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686854623705443087831297 515140967779082315873473)
          ·
            refine ⟨386355725834311736905105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515140967779082315873473 386355725834311736905105)
            ·
              refine ⟨289766794375733802678829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386355725834311736905105 289766794375733802678829)
              ·
                refine ⟨108662547890900176004561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289766794375733802678829 108662547890900176004561)
                ·
                  rfl

theorem cell19_357108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_357108 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357108 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357108 prefixEnd_357108 := by exact prefixLift 357108
  have htrace : WordTrace (prefixWord ++ tailWord_357108) baseStart_357108 baseEnd_357108 := by
    simpa [prefixWord, tailWord_357108, baseEnd_357108] using wordTrace_append hprefix tailTrace_357108
  have hstable : (prefixWord ++ tailWord_357108).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357108).length < 2 ^ (prefixWord ++ tailWord_357108).sum := by decide
  have hdescent : baseEnd_357108 < baseStart_357108 := by decide
  rcases family_descends (prefixWord ++ tailWord_357108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357116 : List Nat := [2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_357116 : Nat := 118140960795 + 357116 * 2 ^ 59
def prefixEnd_357116 : Nat := 4983230072969 + 3 ^ 40 * 357116 * 2
def baseEnd_357116 : Nat := 108664982169558527826761

theorem tailTrace_357116 : CollatzResearch.WordTrace tailWord_357116 prefixEnd_357116 108664982169558527826761 := by
  unfold tailWord_357116
  simp only [CollatzResearch.WordTrace]
  refine ⟨6512545287118598701101601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8683393716158131601468801 6512545287118598701101601)
  ·
    refine ⟨4884408965338949025826201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6512545287118598701101601 4884408965338949025826201)
    ·
      refine ⟨3663306724004211769369651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4884408965338949025826201 3663306724004211769369651)
      ·
        refine ⟨5494960086006317654054477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3663306724004211769369651 5494960086006317654054477)
        ·
          refine ⟨2060610032252369120270429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5494960086006317654054477 2060610032252369120270429)
          ·
            refine ⟨772728762094638420101411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2060610032252369120270429 772728762094638420101411)
            ·
              refine ⟨1159093143141957630152117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772728762094638420101411 1159093143141957630152117)
              ·
                refine ⟨108664982169558527826761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1159093143141957630152117 108664982169558527826761)
                ·
                  rfl

theorem cell19_357116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_357116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357116 prefixEnd_357116 := by exact prefixLift 357116
  have htrace : WordTrace (prefixWord ++ tailWord_357116) baseStart_357116 baseEnd_357116 := by
    simpa [prefixWord, tailWord_357116, baseEnd_357116] using wordTrace_append hprefix tailTrace_357116
  have hstable : (prefixWord ++ tailWord_357116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357116).length < 2 ^ (prefixWord ++ tailWord_357116).sum := by decide
  have hdescent : baseEnd_357116 < baseStart_357116 := by decide
  rcases family_descends (prefixWord ++ tailWord_357116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357137 : List Nat := [1, 2, 2, 1, 1, 3, 9]
def baseStart_357137 : Nat := 118140960795 + 357137 * 2 ^ 59
def prefixEnd_357137 : Nat := 4983230072969 + 3 ^ 40 * 357137 * 2
def baseEnd_357137 : Nat := 36223790717012233786679

theorem tailTrace_357137 : CollatzResearch.WordTrace tailWord_357137 prefixEnd_357137 36223790717012233786679 := by
  unfold tailWord_357137
  simp only [CollatzResearch.WordTrace]
  refine ⟨13025856507161117988717665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8683904338107411992478443 13025856507161117988717665)
  ·
    refine ⟨9769392380370838491538249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13025856507161117988717665 9769392380370838491538249)
    ·
      refine ⟨7327044285278128868653687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9769392380370838491538249 7327044285278128868653687)
      ·
        refine ⟨10990566427917193302980531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7327044285278128868653687 10990566427917193302980531)
        ·
          refine ⟨16485849641875789954470797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10990566427917193302980531 16485849641875789954470797)
          ·
            refine ⟨6182193615703421232926549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16485849641875789954470797 6182193615703421232926549)
            ·
              refine ⟨36223790717012233786679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6182193615703421232926549 36223790717012233786679)
              ·
                rfl

theorem cell19_357137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_357137 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357137 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357137 prefixEnd_357137 := by exact prefixLift 357137
  have htrace : WordTrace (prefixWord ++ tailWord_357137) baseStart_357137 baseEnd_357137 := by
    simpa [prefixWord, tailWord_357137, baseEnd_357137] using wordTrace_append hprefix tailTrace_357137
  have hstable : (prefixWord ++ tailWord_357137).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357137).length < 2 ^ (prefixWord ++ tailWord_357137).sum := by decide
  have hdescent : baseEnd_357137 < baseStart_357137 := by decide
  rcases family_descends (prefixWord ++ tailWord_357137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357154 : List Nat := [3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_357154 : Nat := 118140960795 + 357154 * 2 ^ 59
def prefixEnd_357154 : Nat := 4983230072969 + 3 ^ 40 * 357154 * 2
def baseEnd_357154 : Nat := 108676544993185698982213

theorem tailTrace_357154 : CollatzResearch.WordTrace tailWord_357154 prefixEnd_357154 108676544993185698982213 := by
  unfold tailWord_357154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256619137024882473021629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8684317698733019928057677 3256619137024882473021629)
  ·
    refine ⟨1221232176384330927383111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3256619137024882473021629 1221232176384330927383111)
    ·
      refine ⟨1831848264576496391074667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1221232176384330927383111 1831848264576496391074667)
      ·
        refine ⟨2747772396864744586612001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831848264576496391074667 2747772396864744586612001)
        ·
          refine ⟨2060829297648558439959001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2747772396864744586612001 2060829297648558439959001)
          ·
            refine ⟨1545621973236418829969251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2060829297648558439959001 1545621973236418829969251)
            ·
              refine ⟨2318432959854628244953877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545621973236418829969251 2318432959854628244953877)
              ·
                refine ⟨108676544993185698982213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2318432959854628244953877 108676544993185698982213)
                ·
                  rfl

theorem cell19_357154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_357154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357154 prefixEnd_357154 := by exact prefixLift 357154
  have htrace : WordTrace (prefixWord ++ tailWord_357154) baseStart_357154 baseEnd_357154 := by
    simpa [prefixWord, tailWord_357154, baseEnd_357154] using wordTrace_append hprefix tailTrace_357154
  have hstable : (prefixWord ++ tailWord_357154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357154).length < 2 ^ (prefixWord ++ tailWord_357154).sum := by decide
  have hdescent : baseEnd_357154 < baseStart_357154 := by decide
  rcases family_descends (prefixWord ++ tailWord_357154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357173 : List Nat := [1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_357173 : Nat := 118140960795 + 357173 * 2 ^ 59
def prefixEnd_357173 : Nat := 4983230072969 + 3 ^ 40 * 357173 * 2
def baseEnd_357173 : Nat := 108682326404999284559939

theorem tailTrace_357173 : CollatzResearch.WordTrace tailWord_357173 prefixEnd_357173 108682326404999284559939 := by
  unfold tailWord_357173
  simp only [CollatzResearch.WordTrace]
  refine ⟨13027169535030696137028173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8684779690020464091352115 13027169535030696137028173)
  ·
    refine ⟨4885188575636511051385565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13027169535030696137028173 4885188575636511051385565)
    ·
      refine ⟨1831945715863691644269587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4885188575636511051385565 1831945715863691644269587)
      ·
        refine ⟨2747918573795537466404381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831945715863691644269587 2747918573795537466404381)
        ·
          refine ⟨1030469465173326549901643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2747918573795537466404381 1030469465173326549901643)
          ·
            refine ⟨1545704197759989824852465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030469465173326549901643 1545704197759989824852465)
            ·
              refine ⟨1159278148319992368639349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1545704197759989824852465 1159278148319992368639349)
              ·
                refine ⟨108682326404999284559939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1159278148319992368639349 108682326404999284559939)
                ·
                  rfl

theorem cell19_357173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_357173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357173 prefixEnd_357173 := by exact prefixLift 357173
  have htrace : WordTrace (prefixWord ++ tailWord_357173) baseStart_357173 baseEnd_357173 := by
    simpa [prefixWord, tailWord_357173, baseEnd_357173] using wordTrace_append hprefix tailTrace_357173
  have hstable : (prefixWord ++ tailWord_357173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357173).length < 2 ^ (prefixWord ++ tailWord_357173).sum := by decide
  have hdescent : baseEnd_357173 < baseStart_357173 := by decide
  rcases family_descends (prefixWord ++ tailWord_357173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357175 : List Nat := [1, 1, 3, 1, 2, 1, 3, 7]
def baseStart_357175 : Nat := 118140960795 + 357175 * 2 ^ 59
def prefixEnd_357175 : Nat := 4983230072969 + 3 ^ 40 * 357175 * 2
def baseEnd_357175 : Nat := 108682934974663872515489

theorem tailTrace_357175 : CollatzResearch.WordTrace tailWord_357175 prefixEnd_357175 108682934974663872515489 := by
  unfold tailWord_357175
  simp only [CollatzResearch.WordTrace]
  refine ⟨13027242481023450478600979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8684828320682300319067319 13027242481023450478600979)
  ·
    refine ⟨19540863721535175717901469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13027242481023450478600979 19540863721535175717901469)
    ·
      refine ⟨7327823895575690894213051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19540863721535175717901469 7327823895575690894213051)
      ·
        refine ⟨10991735843363536341319577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7327823895575690894213051 10991735843363536341319577)
        ·
          refine ⟨8243801882522652255989683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10991735843363536341319577 8243801882522652255989683)
          ·
            refine ⟨12365702823783978383984525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8243801882522652255989683 12365702823783978383984525)
            ·
              refine ⟨4637138558918991893994197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12365702823783978383984525 4637138558918991893994197)
              ·
                refine ⟨108682934974663872515489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4637138558918991893994197 108682934974663872515489)
                ·
                  rfl

theorem cell19_357175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 7].length) (baseStart_357175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357175 prefixEnd_357175 := by exact prefixLift 357175
  have htrace : WordTrace (prefixWord ++ tailWord_357175) baseStart_357175 baseEnd_357175 := by
    simpa [prefixWord, tailWord_357175, baseEnd_357175] using wordTrace_append hprefix tailTrace_357175
  have hstable : (prefixWord ++ tailWord_357175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357175).length < 2 ^ (prefixWord ++ tailWord_357175).sum := by decide
  have hdescent : baseEnd_357175 < baseStart_357175 := by decide
  rcases family_descends (prefixWord ++ tailWord_357175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357188 : List Nat := [2, 3, 4, 2, 2, 6]
def baseStart_357188 : Nat := 118140960795 + 357188 * 2 ^ 59
def prefixEnd_357188 : Nat := 4983230072969 + 3 ^ 40 * 357188 * 2
def baseEnd_357188 : Nat := 12076321186387077136285

theorem tailTrace_357188 : CollatzResearch.WordTrace tailWord_357188 prefixEnd_357188 12076321186387077136285 := by
  unfold tailWord_357188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6513858314988176849412109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8685144419984235799216145 6513858314988176849412109)
  ·
    refine ⟨2442696868120566318529541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6513858314988176849412109 2442696868120566318529541)
    ·
      refine ⟨458005662772606184724289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2442696868120566318529541 458005662772606184724289)
      ·
        refine ⟨343504247079454638543217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458005662772606184724289 343504247079454638543217)
        ·
          refine ⟨257628185309590978907413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343504247079454638543217 257628185309590978907413)
          ·
            refine ⟨12076321186387077136285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 257628185309590978907413 12076321186387077136285)
            ·
              rfl

theorem cell19_357188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 6].length) (baseStart_357188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357188 prefixEnd_357188 := by exact prefixLift 357188
  have htrace : WordTrace (prefixWord ++ tailWord_357188) baseStart_357188 baseEnd_357188 := by
    simpa [prefixWord, tailWord_357188, baseEnd_357188] using wordTrace_append hprefix tailTrace_357188
  have hstable : (prefixWord ++ tailWord_357188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357188).length < 2 ^ (prefixWord ++ tailWord_357188).sum := by decide
  have hdescent : baseEnd_357188 < baseStart_357188 := by decide
  rcases family_descends (prefixWord ++ tailWord_357188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357190 : List Nat := [6, 1, 1, 2, 9]
def baseStart_357190 : Nat := 118140960795 + 357190 * 2 ^ 59
def prefixEnd_357190 : Nat := 4983230072969 + 3 ^ 40 * 357190 * 2
def baseEnd_357190 : Nat := 4025462935079566006745

theorem tailTrace_357190 : CollatzResearch.WordTrace tailWord_357190 prefixEnd_357190 4025462935079566006745 := by
  unfold tailWord_357190
  simp only [CollatzResearch.WordTrace]
  refine ⟨407118424249034626262407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8685193050646072026931349 407118424249034626262407)
  ·
    refine ⟨610677636373551939393611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 407118424249034626262407 610677636373551939393611)
    ·
      refine ⟨916016454560327909090417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610677636373551939393611 916016454560327909090417)
      ·
        refine ⟨687012340920245931817813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 916016454560327909090417 687012340920245931817813)
        ·
          refine ⟨4025462935079566006745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 687012340920245931817813 4025462935079566006745)
          ·
            rfl

theorem cell19_357190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 9].length) (baseStart_357190 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357190 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357190 prefixEnd_357190 := by exact prefixLift 357190
  have htrace : WordTrace (prefixWord ++ tailWord_357190) baseStart_357190 baseEnd_357190 := by
    simpa [prefixWord, tailWord_357190, baseEnd_357190] using wordTrace_append hprefix tailTrace_357190
  have hstable : (prefixWord ++ tailWord_357190).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357190).length < 2 ^ (prefixWord ++ tailWord_357190).sum := by decide
  have hdescent : baseEnd_357190 < baseStart_357190 := by decide
  rcases family_descends (prefixWord ++ tailWord_357190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357232 : List Nat := [2, 1, 1, 1, 4, 1, 2, 7]
def baseStart_357232 : Nat := 118140960795 + 357232 * 2 ^ 59
def prefixEnd_357232 : Nat := 4983230072969 + 3 ^ 40 * 357232 * 2
def baseEnd_357232 : Nat := 108700279210104629248667

theorem tailTrace_357232 : CollatzResearch.WordTrace tailWord_357232 prefixEnd_357232 108700279210104629248667 := by
  unfold tailWord_357232
  simp only [CollatzResearch.WordTrace]
  refine ⟨6514660720908474606712975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8686214294544632808950633 6514660720908474606712975)
  ·
    refine ⟨9771991081362711910069463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6514660720908474606712975 9771991081362711910069463)
    ·
      refine ⟨14657986622044067865104195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9771991081362711910069463 14657986622044067865104195)
      ·
        refine ⟨21986979933066101797656293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14657986622044067865104195 21986979933066101797656293)
        ·
          refine ⟨4122558737449894087060555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21986979933066101797656293 4122558737449894087060555)
          ·
            refine ⟨6183838106174841130590833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4122558737449894087060555 6183838106174841130590833)
            ·
              refine ⟨4637878579631130847943125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6183838106174841130590833 4637878579631130847943125)
              ·
                refine ⟨108700279210104629248667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4637878579631130847943125 108700279210104629248667)
                ·
                  rfl

theorem cell19_357232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_357232 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357232 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357232 prefixEnd_357232 := by exact prefixLift 357232
  have htrace : WordTrace (prefixWord ++ tailWord_357232) baseStart_357232 baseEnd_357232 := by
    simpa [prefixWord, tailWord_357232, baseEnd_357232] using wordTrace_append hprefix tailTrace_357232
  have hstable : (prefixWord ++ tailWord_357232).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357232).length < 2 ^ (prefixWord ++ tailWord_357232).sum := by decide
  have hdescent : baseEnd_357232 < baseStart_357232 := by decide
  rcases family_descends (prefixWord ++ tailWord_357232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357251 : List Nat := [1, 1, 1, 3, 4, 1, 8]
def baseStart_357251 : Nat := 118140960795 + 357251 * 2 ^ 59
def prefixEnd_357251 : Nat := 4983230072969 + 3 ^ 40 * 357251 * 2
def baseEnd_357251 : Nat := 36235353540639404942131

theorem tailTrace_357251 : CollatzResearch.WordTrace tailWord_357251 prefixEnd_357251 36235353540639404942131 := by
  unfold tailWord_357251
  simp only [CollatzResearch.WordTrace]
  refine ⟨13030014428748115458367607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8686676285832076972245071 13030014428748115458367607)
  ·
    refine ⟨19545021643122173187551411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13030014428748115458367607 19545021643122173187551411)
    ·
      refine ⟨29317532464683259781327117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19545021643122173187551411 29317532464683259781327117)
      ·
        refine ⟨10994074674256222417997669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29317532464683259781327117 10994074674256222417997669)
        ·
          refine ⟨2061389001423041703374563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10994074674256222417997669 2061389001423041703374563)
          ·
            refine ⟨3092083502134562555061845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061389001423041703374563 3092083502134562555061845)
            ·
              refine ⟨36235353540639404942131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3092083502134562555061845 36235353540639404942131)
              ·
                rfl

theorem cell19_357251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_357251 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357251 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357251 prefixEnd_357251 := by exact prefixLift 357251
  have htrace : WordTrace (prefixWord ++ tailWord_357251) baseStart_357251 baseEnd_357251 := by
    simpa [prefixWord, tailWord_357251, baseEnd_357251] using wordTrace_append hprefix tailTrace_357251
  have hstable : (prefixWord ++ tailWord_357251).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357251).length < 2 ^ (prefixWord ++ tailWord_357251).sum := by decide
  have hdescent : baseEnd_357251 < baseStart_357251 := by decide
  rcases family_descends (prefixWord ++ tailWord_357251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357268 : List Nat := [2, 4, 2, 1, 1, 1, 2, 6]
def baseStart_357268 : Nat := 118140960795 + 357268 * 2 ^ 59
def prefixEnd_357268 : Nat := 4983230072969 + 3 ^ 40 * 357268 * 2
def baseEnd_357268 : Nat := 108711233464067212448569

theorem tailTrace_357268 : CollatzResearch.WordTrace tailWord_357268 prefixEnd_357268 108711233464067212448569 := by
  unfold tailWord_357268
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515317234843263680868229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8687089646457684907824305 6515317234843263680868229)
  ·
    refine ⟨1221621981533111940162793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6515317234843263680868229 1221621981533111940162793)
    ·
      refine ⟨916216486149833955122095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1221621981533111940162793 916216486149833955122095)
      ·
        refine ⟨1374324729224750932683143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916216486149833955122095 1374324729224750932683143)
        ·
          refine ⟨2061487093837126399024715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374324729224750932683143 2061487093837126399024715)
          ·
            refine ⟨3092230640755689598537073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061487093837126399024715 3092230640755689598537073)
            ·
              refine ⟨2319172980566767198902805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3092230640755689598537073 2319172980566767198902805)
              ·
                refine ⟨108711233464067212448569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2319172980566767198902805 108711233464067212448569)
                ·
                  rfl

theorem cell19_357268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_357268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357268 prefixEnd_357268 := by exact prefixLift 357268
  have htrace : WordTrace (prefixWord ++ tailWord_357268) baseStart_357268 baseEnd_357268 := by
    simpa [prefixWord, tailWord_357268, baseEnd_357268] using wordTrace_append hprefix tailTrace_357268
  have hstable : (prefixWord ++ tailWord_357268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357268).length < 2 ^ (prefixWord ++ tailWord_357268).sum := by decide
  have hdescent : baseEnd_357268 < baseStart_357268 := by decide
  rcases family_descends (prefixWord ++ tailWord_357268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357289 : List Nat := [1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_357289 : Nat := 118140960795 + 357289 * 2 ^ 59
def prefixEnd_357289 : Nat := 4983230072969 + 3 ^ 40 * 357289 * 2
def baseEnd_357289 : Nat := 108717623445545385981845

theorem tailTrace_357289 : CollatzResearch.WordTrace tailWord_357289 prefixEnd_357289 108717623445545385981845 := by
  unfold tailWord_357289
  simp only [CollatzResearch.WordTrace]
  refine ⟨13031400402610447948250921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8687600268406965298833947 13031400402610447948250921)
  ·
    refine ⟨9773550301957835961188191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13031400402610447948250921 9773550301957835961188191)
    ·
      refine ⟨14660325452936753941782287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9773550301957835961188191 14660325452936753941782287)
      ·
        refine ⟨21990488179405130912673431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14660325452936753941782287 21990488179405130912673431)
        ·
          refine ⟨32985732269107696369010147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21990488179405130912673431 32985732269107696369010147)
          ·
            refine ⟨49478598403661544553515221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32985732269107696369010147 49478598403661544553515221)
            ·
              refine ⟨1159654650085817450473013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 49478598403661544553515221 1159654650085817450473013)
              ·
                refine ⟨108717623445545385981845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1159654650085817450473013 108717623445545385981845)
                ·
                  rfl

theorem cell19_357289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_357289 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357289 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357289 prefixEnd_357289 := by exact prefixLift 357289
  have htrace : WordTrace (prefixWord ++ tailWord_357289) baseStart_357289 baseEnd_357289 := by
    simpa [prefixWord, tailWord_357289, baseEnd_357289] using wordTrace_append hprefix tailTrace_357289
  have hstable : (prefixWord ++ tailWord_357289).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357289).length < 2 ^ (prefixWord ++ tailWord_357289).sum := by decide
  have hdescent : baseEnd_357289 < baseStart_357289 := by decide
  rcases family_descends (prefixWord ++ tailWord_357289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357327 : List Nat := [1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_357327 : Nat := 118140960795 + 357327 * 2 ^ 59
def prefixEnd_357327 : Nat := 4983230072969 + 3 ^ 40 * 357327 * 2
def baseEnd_357327 : Nat := 108729186269172557137297

theorem tailTrace_357327 : CollatzResearch.WordTrace tailWord_357327 prefixEnd_357327 108729186269172557137297 := by
  unfold tailWord_357327
  simp only [CollatzResearch.WordTrace]
  refine ⟨13032786376472780438134235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8688524250981853625422823 13032786376472780438134235)
  ·
    refine ⟨19549179564709170657201353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13032786376472780438134235 19549179564709170657201353)
    ·
      refine ⟨14661884673531877992901015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19549179564709170657201353 14661884673531877992901015)
      ·
        refine ⟨21992827010297816989351523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14661884673531877992901015 21992827010297816989351523)
        ·
          refine ⟨32989240515446725484027285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21992827010297816989351523 32989240515446725484027285)
          ·
            refine ⟨1546370649161565257063779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32989240515446725484027285 1546370649161565257063779)
            ·
              refine ⟨2319555973742347885595669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546370649161565257063779 2319555973742347885595669)
              ·
                refine ⟨108729186269172557137297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2319555973742347885595669 108729186269172557137297)
                ·
                  rfl

theorem cell19_357327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_357327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357327 prefixEnd_357327 := by exact prefixLift 357327
  have htrace : WordTrace (prefixWord ++ tailWord_357327) baseStart_357327 baseEnd_357327 := by
    simpa [prefixWord, tailWord_357327, baseEnd_357327] using wordTrace_append hprefix tailTrace_357327
  have hstable : (prefixWord ++ tailWord_357327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357327).length < 2 ^ (prefixWord ++ tailWord_357327).sum := by decide
  have hdescent : baseEnd_357327 < baseStart_357327 := by decide
  rcases family_descends (prefixWord ++ tailWord_357327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357399 : List Nat := [1, 1, 3, 5, 1, 2, 3, 3]
def baseStart_357399 : Nat := 118140960795 + 357399 * 2 ^ 59
def prefixEnd_357399 : Nat := 4983230072969 + 3 ^ 40 * 357399 * 2
def baseEnd_357399 : Nat := 108751094777097723537101

theorem tailTrace_357399 : CollatzResearch.WordTrace tailWord_357399 prefixEnd_357399 108751094777097723537101 := by
  unfold tailWord_357399
  simp only [CollatzResearch.WordTrace]
  refine ⟨13035412432211936734755251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8690274954807957823170167 13035412432211936734755251)
  ·
    refine ⟨19553118648317905102132877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13035412432211936734755251 19553118648317905102132877)
    ·
      refine ⟨7332419493119214413299829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19553118648317905102132877 7332419493119214413299829)
      ·
        refine ⟨687414327479926351246859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7332419493119214413299829 687414327479926351246859)
        ·
          refine ⟨1031121491219889526870289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687414327479926351246859 1031121491219889526870289)
          ·
            refine ⟨773341118414917145152717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031121491219889526870289 773341118414917145152717)
            ·
              refine ⟨290002919405593929432269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 773341118414917145152717 290002919405593929432269)
              ·
                refine ⟨108751094777097723537101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290002919405593929432269 108751094777097723537101)
                ·
                  rfl

theorem cell19_357399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_357399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357399 prefixEnd_357399 := by exact prefixLift 357399
  have htrace : WordTrace (prefixWord ++ tailWord_357399) baseStart_357399 baseEnd_357399 := by
    simpa [prefixWord, tailWord_357399, baseEnd_357399] using wordTrace_append hprefix tailTrace_357399
  have hstable : (prefixWord ++ tailWord_357399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357399).length < 2 ^ (prefixWord ++ tailWord_357399).sum := by decide
  have hdescent : baseEnd_357399 < baseStart_357399 := by decide
  rcases family_descends (prefixWord ++ tailWord_357399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357458 : List Nat := [3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_357458 : Nat := 118140960795 + 357458 * 2 ^ 59
def prefixEnd_357458 : Nat := 4983230072969 + 3 ^ 40 * 357458 * 2
def baseEnd_357458 : Nat := 108769047582203068225829

theorem tailTrace_357458 : CollatzResearch.WordTrace tailWord_357458 prefixEnd_357458 108769047582203068225829 := by
  unfold tailWord_357458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3259391084749547452788257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8691709559332126540768685 3259391084749547452788257)
  ·
    refine ⟨2444543313562160589591193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3259391084749547452788257 2444543313562160589591193)
    ·
      refine ⟨1833407485171620442193395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2444543313562160589591193 1833407485171620442193395)
      ·
        refine ⟨2750111227757430663290093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833407485171620442193395 2750111227757430663290093)
        ·
          refine ⟨1031291710409036498733785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2750111227757430663290093 1031291710409036498733785)
          ·
            refine ⟨773468782806777374050339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031291710409036498733785 773468782806777374050339)
            ·
              refine ⟨1160203174210166061075509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773468782806777374050339 1160203174210166061075509)
              ·
                refine ⟨108769047582203068225829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1160203174210166061075509 108769047582203068225829)
                ·
                  rfl

theorem cell19_357458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_357458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357458 prefixEnd_357458 := by exact prefixLift 357458
  have htrace : WordTrace (prefixWord ++ tailWord_357458) baseStart_357458 baseEnd_357458 := by
    simpa [prefixWord, tailWord_357458, baseEnd_357458] using wordTrace_append hprefix tailTrace_357458
  have hstable : (prefixWord ++ tailWord_357458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357458).length < 2 ^ (prefixWord ++ tailWord_357458).sum := by decide
  have hdescent : baseEnd_357458 < baseStart_357458 := by decide
  rcases family_descends (prefixWord ++ tailWord_357458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357479 : List Nat := [1, 1, 5, 1, 1, 3, 7]
def baseStart_357479 : Nat := 118140960795 + 357479 * 2 ^ 59
def prefixEnd_357479 : Nat := 4983230072969 + 3 ^ 40 * 357479 * 2
def baseEnd_357479 : Nat := 36258479187893747253035

theorem tailTrace_357479 : CollatzResearch.WordTrace tailWord_357479 prefixEnd_357479 36258479187893747253035 := by
  unfold tailWord_357479
  simp only [CollatzResearch.WordTrace]
  refine ⟨13038330271922110397667491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8692220181281406931778327 13038330271922110397667491)
  ·
    refine ⟨19557495407883165596501237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13038330271922110397667491 19557495407883165596501237)
    ·
      refine ⟨1833515194489046774671991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19557495407883165596501237 1833515194489046774671991)
      ·
        refine ⟨2750272791733570162007987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833515194489046774671991 2750272791733570162007987)
        ·
          refine ⟨4125409187600355243011981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750272791733570162007987 4125409187600355243011981)
          ·
            refine ⟨1547028445350133216129493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4125409187600355243011981 1547028445350133216129493)
            ·
              refine ⟨36258479187893747253035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1547028445350133216129493 36258479187893747253035)
              ·
                rfl

theorem cell19_357479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_357479 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357479 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357479 prefixEnd_357479 := by exact prefixLift 357479
  have htrace : WordTrace (prefixWord ++ tailWord_357479) baseStart_357479 baseEnd_357479 := by
    simpa [prefixWord, tailWord_357479, baseEnd_357479] using wordTrace_append hprefix tailTrace_357479
  have hstable : (prefixWord ++ tailWord_357479).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357479).length < 2 ^ (prefixWord ++ tailWord_357479).sum := by decide
  have hdescent : baseEnd_357479 < baseStart_357479 := by decide
  rcases family_descends (prefixWord ++ tailWord_357479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357534 : List Nat := [4, 3, 1, 1, 2, 8]
def baseStart_357534 : Nat := 118140960795 + 357534 * 2 ^ 59
def prefixEnd_357534 : Nat := 4983230072969 + 3 ^ 40 * 357534 * 2
def baseEnd_357534 : Nat := 12088019247717490059637

theorem tailTrace_357534 : CollatzResearch.WordTrace tailWord_357534 prefixEnd_357534 12088019247717490059637 := by
  unfold tailWord_357534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630042035840356848864957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8693557524481903193946437 1630042035840356848864957)
  ·
    refine ⟨611265763440133818324359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1630042035840356848864957 611265763440133818324359)
    ·
      refine ⟨916898645160200727486539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 611265763440133818324359 916898645160200727486539)
      ·
        refine ⟨1375347967740301091229809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916898645160200727486539 1375347967740301091229809)
        ·
          refine ⟨1031510975805225818422357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1375347967740301091229809 1031510975805225818422357)
          ·
            refine ⟨12088019247717490059637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1031510975805225818422357 12088019247717490059637)
            ·
              rfl

theorem cell19_357534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 8].length) (baseStart_357534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357534 prefixEnd_357534 := by exact prefixLift 357534
  have htrace : WordTrace (prefixWord ++ tailWord_357534) baseStart_357534 baseEnd_357534 := by
    simpa [prefixWord, tailWord_357534, baseEnd_357534] using wordTrace_append hprefix tailTrace_357534
  have hstable : (prefixWord ++ tailWord_357534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357534).length < 2 ^ (prefixWord ++ tailWord_357534).sum := by decide
  have hdescent : baseEnd_357534 < baseStart_357534 := by decide
  rcases family_descends (prefixWord ++ tailWord_357534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357549 : List Nat := [1, 5, 2, 1, 4, 1, 1, 4]
def baseStart_357549 : Nat := 118140960795 + 357549 * 2 ^ 59
def prefixEnd_357549 : Nat := 4983230072969 + 3 ^ 40 * 357549 * 2
def baseEnd_357549 : Nat := 108796737501941820203359

theorem tailTrace_357549 : CollatzResearch.WordTrace tailWord_357549 prefixEnd_357549 108796737501941820203359 := by
  unfold tailWord_357549
  simp only [CollatzResearch.WordTrace]
  refine ⟨13040883381668512352715701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8693922254445674901810467 13040883381668512352715701)
  ·
    refine ⟨1222582817031423033067097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13040883381668512352715701 1222582817031423033067097)
    ·
      refine ⟨916937112773567274800323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1222582817031423033067097 916937112773567274800323)
      ·
        refine ⟨1375405669160350912200485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916937112773567274800323 1375405669160350912200485)
        ·
          refine ⟨257888562967565796037591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1375405669160350912200485 257888562967565796037591)
          ·
            refine ⟨386832844451348694056387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257888562967565796037591 386832844451348694056387)
            ·
              refine ⟨580249266677023041084581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386832844451348694056387 580249266677023041084581)
              ·
                refine ⟨108796737501941820203359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580249266677023041084581 108796737501941820203359)
                ·
                  rfl

theorem cell19_357549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 4].length) (baseStart_357549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357549 prefixEnd_357549 := by exact prefixLift 357549
  have htrace : WordTrace (prefixWord ++ tailWord_357549) baseStart_357549 baseEnd_357549 := by
    simpa [prefixWord, tailWord_357549, baseEnd_357549] using wordTrace_append hprefix tailTrace_357549
  have hstable : (prefixWord ++ tailWord_357549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357549).length < 2 ^ (prefixWord ++ tailWord_357549).sum := by decide
  have hdescent : baseEnd_357549 < baseStart_357549 := by decide
  rcases family_descends (prefixWord ++ tailWord_357549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357553 : List Nat := [1, 2, 2, 5, 1, 1, 3, 4]
def baseStart_357553 : Nat := 118140960795 + 357553 * 2 ^ 59
def prefixEnd_357553 : Nat := 4983230072969 + 3 ^ 40 * 357553 * 2
def baseEnd_357553 : Nat := 108797954641270996114459

theorem tailTrace_357553 : CollatzResearch.WordTrace tailWord_357553 prefixEnd_357553 108797954641270996114459 := by
  unfold tailWord_357553
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041029273654021035861313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8694019515769347357240875 13041029273654021035861313)
  ·
    refine ⟨9780771955240515776895985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13041029273654021035861313 9780771955240515776895985)
    ·
      refine ⟨7335578966430386832671989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9780771955240515776895985 7335578966430386832671989)
      ·
        refine ⟨687710528102848765562999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7335578966430386832671989 687710528102848765562999)
        ·
          refine ⟨1031565792154273148344499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687710528102848765562999 1031565792154273148344499)
          ·
            refine ⟨1547348688231409722516749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031565792154273148344499 1547348688231409722516749)
            ·
              refine ⟨580255758086778645943781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1547348688231409722516749 580255758086778645943781)
              ·
                refine ⟨108797954641270996114459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580255758086778645943781 108797954641270996114459)
                ·
                  rfl

theorem cell19_357553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 4].length) (baseStart_357553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357553 prefixEnd_357553 := by exact prefixLift 357553
  have htrace : WordTrace (prefixWord ++ tailWord_357553) baseStart_357553 baseEnd_357553 := by
    simpa [prefixWord, tailWord_357553, baseEnd_357553] using wordTrace_append hprefix tailTrace_357553
  have hstable : (prefixWord ++ tailWord_357553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357553).length < 2 ^ (prefixWord ++ tailWord_357553).sum := by decide
  have hdescent : baseEnd_357553 < baseStart_357553 := by decide
  rcases family_descends (prefixWord ++ tailWord_357553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357555 : List Nat := [1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_357555 : Nat := 118140960795 + 357555 * 2 ^ 59
def prefixEnd_357555 : Nat := 4983230072969 + 3 ^ 40 * 357555 * 2
def baseEnd_357555 : Nat := 108798563210935584070009

theorem tailTrace_357555 : CollatzResearch.WordTrace tailWord_357555 prefixEnd_357555 108798563210935584070009 := by
  unfold tailWord_357555
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041102219646775377434119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8694068146431183584956079 13041102219646775377434119)
  ·
    refine ⟨19561653329470163066151179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13041102219646775377434119 19561653329470163066151179)
    ·
      refine ⟨29342479994205244599226769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19561653329470163066151179 29342479994205244599226769)
      ·
        refine ⟨22006859995653933449420077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29342479994205244599226769 22006859995653933449420077)
        ·
          refine ⟨8252572498370225043532529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22006859995653933449420077 8252572498370225043532529)
          ·
            refine ⟨6189429373777668782649397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8252572498370225043532529 6189429373777668782649397)
            ·
              refine ⟨580259003791656448373381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6189429373777668782649397 580259003791656448373381)
              ·
                refine ⟨108798563210935584070009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580259003791656448373381 108798563210935584070009)
                ·
                  rfl

theorem cell19_357555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_357555 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357555 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357555 prefixEnd_357555 := by exact prefixLift 357555
  have htrace : WordTrace (prefixWord ++ tailWord_357555) baseStart_357555 baseEnd_357555 := by
    simpa [prefixWord, tailWord_357555, baseEnd_357555] using wordTrace_append hprefix tailTrace_357555
  have hstable : (prefixWord ++ tailWord_357555).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357555).length < 2 ^ (prefixWord ++ tailWord_357555).sum := by decide
  have hdescent : baseEnd_357555 < baseStart_357555 := by decide
  rcases family_descends (prefixWord ++ tailWord_357555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357631 : List Nat := [1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_357631 : Nat := 118140960795 + 357631 * 2 ^ 59
def prefixEnd_357631 : Nat := 4983230072969 + 3 ^ 40 * 357631 * 2
def baseEnd_357631 : Nat := 108821688858189926380913

theorem tailTrace_357631 : CollatzResearch.WordTrace tailWord_357631 prefixEnd_357631 108821688858189926380913 := by
  unfold tailWord_357631
  simp only [CollatzResearch.WordTrace]
  refine ⟨13043874167371440357200747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8695916111580960238133831 13043874167371440357200747)
  ·
    refine ⟨19565811251057160535801121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13043874167371440357200747 19565811251057160535801121)
    ·
      refine ⟨14674358438292870401850841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19565811251057160535801121 14674358438292870401850841)
      ·
        refine ⟨11005768828719652801388131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14674358438292870401850841 11005768828719652801388131)
        ·
          refine ⟨16508653243079479202082197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11005768828719652801388131 16508653243079479202082197)
          ·
            refine ⟨773843120769350587597603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16508653243079479202082197 773843120769350587597603)
            ·
              refine ⟨1160764681154025881396405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773843120769350587597603 1160764681154025881396405)
              ·
                refine ⟨108821688858189926380913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1160764681154025881396405 108821688858189926380913)
                ·
                  rfl

theorem cell19_357631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_357631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357631 prefixEnd_357631 := by exact prefixLift 357631
  have htrace : WordTrace (prefixWord ++ tailWord_357631) baseStart_357631 baseEnd_357631 := by
    simpa [prefixWord, tailWord_357631, baseEnd_357631] using wordTrace_append hprefix tailTrace_357631
  have hstable : (prefixWord ++ tailWord_357631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357631).length < 2 ^ (prefixWord ++ tailWord_357631).sum := by decide
  have hdescent : baseEnd_357631 < baseStart_357631 := by decide
  rcases family_descends (prefixWord ++ tailWord_357631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357669 : List Nat := [1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_357669 : Nat := 118140960795 + 357669 * 2 ^ 59
def prefixEnd_357669 : Nat := 4983230072969 + 3 ^ 40 * 357669 * 2
def baseEnd_357669 : Nat := 108833251681817097536365

theorem tailTrace_357669 : CollatzResearch.WordTrace tailWord_357669 prefixEnd_357669 108833251681817097536365 := by
  unfold tailWord_357669
  simp only [CollatzResearch.WordTrace]
  refine ⟨13045260141233772847084061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8696840094155848564722707 13045260141233772847084061)
  ·
    refine ⟨4891972552962664817656523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13045260141233772847084061 4891972552962664817656523)
    ·
      refine ⟨7337958829443997226484785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4891972552962664817656523 7337958829443997226484785)
      ·
        refine ⟨5503469122082997919863589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7337958829443997226484785 5503469122082997919863589)
        ·
          refine ⟨1031900460390562109974423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5503469122082997919863589 1031900460390562109974423)
          ·
            refine ⟨1547850690585843164961635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031900460390562109974423 1547850690585843164961635)
            ·
              refine ⟨2321776035878764747442453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547850690585843164961635 2321776035878764747442453)
              ·
                refine ⟨108833251681817097536365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2321776035878764747442453 108833251681817097536365)
                ·
                  rfl

theorem cell19_357669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_357669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357669 prefixEnd_357669 := by exact prefixLift 357669
  have htrace : WordTrace (prefixWord ++ tailWord_357669) baseStart_357669 baseEnd_357669 := by
    simpa [prefixWord, tailWord_357669, baseEnd_357669] using wordTrace_append hprefix tailTrace_357669
  have hstable : (prefixWord ++ tailWord_357669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357669).length < 2 ^ (prefixWord ++ tailWord_357669).sum := by decide
  have hdescent : baseEnd_357669 < baseStart_357669 := by decide
  rcases family_descends (prefixWord ++ tailWord_357669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357764 : List Nat := [2, 3, 2, 1, 1, 4, 6]
def baseStart_357764 : Nat := 118140960795 + 357764 * 2 ^ 59
def prefixEnd_357764 : Nat := 4983230072969 + 3 ^ 40 * 357764 * 2
def baseEnd_357764 : Nat := 36287386246961675141665

theorem tailTrace_357764 : CollatzResearch.WordTrace tailWord_357764 prefixEnd_357764 36287386246961675141665 := by
  unfold tailWord_357764
  simp only [CollatzResearch.WordTrace]
  refine ⟨6524362537944802035896173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8699150050593069381194897 6524362537944802035896173)
  ·
    refine ⟨2446635951729300763461065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6524362537944802035896173 2446635951729300763461065)
    ·
      refine ⟨1834976963796975572595799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2446635951729300763461065 1834976963796975572595799)
      ·
        refine ⟨2752465445695463358893699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1834976963796975572595799 2752465445695463358893699)
        ·
          refine ⟨4128698168543195038340549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2752465445695463358893699 4128698168543195038340549)
          ·
            refine ⟨774130906601849069688853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4128698168543195038340549 774130906601849069688853)
            ·
              refine ⟨36287386246961675141665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 774130906601849069688853 36287386246961675141665)
              ·
                rfl

theorem cell19_357764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_357764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357764 prefixEnd_357764 := by exact prefixLift 357764
  have htrace : WordTrace (prefixWord ++ tailWord_357764) baseStart_357764 baseEnd_357764 := by
    simpa [prefixWord, tailWord_357764, baseEnd_357764] using wordTrace_append hprefix tailTrace_357764
  have hstable : (prefixWord ++ tailWord_357764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357764).length < 2 ^ (prefixWord ++ tailWord_357764).sum := by decide
  have hdescent : baseEnd_357764 < baseStart_357764 := by decide
  rcases family_descends (prefixWord ++ tailWord_357764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357859 : List Nat := [1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_357859 : Nat := 118140960795 + 357859 * 2 ^ 59
def prefixEnd_357859 : Nat := 4983230072969 + 3 ^ 40 * 357859 * 2
def baseEnd_357859 : Nat := 108891065799952953313625

theorem tailTrace_357859 : CollatzResearch.WordTrace tailWord_357859 prefixEnd_357859 108891065799952953313625 := by
  unfold tailWord_357859
  simp only [CollatzResearch.WordTrace]
  refine ⟨13052190010545435296500631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8701460007030290197667087 13052190010545435296500631)
  ·
    refine ⟨19578285015818152944750947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13052190010545435296500631 19578285015818152944750947)
    ·
      refine ⟨29367427523727229417126421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19578285015818152944750947 29367427523727229417126421)
      ·
        refine ⟨1376598165174713878927801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29367427523727229417126421 1376598165174713878927801)
        ·
          refine ⟨1032448623881035409195851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1376598165174713878927801 1032448623881035409195851)
          ·
            refine ⟨1548672935821553113793777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032448623881035409195851 1548672935821553113793777)
            ·
              refine ⟨1161504701866164835345333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1548672935821553113793777 1161504701866164835345333)
              ·
                refine ⟨108891065799952953313625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1161504701866164835345333 108891065799952953313625)
                ·
                  rfl

theorem cell19_357859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_357859 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357859 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357859 prefixEnd_357859 := by exact prefixLift 357859
  have htrace : WordTrace (prefixWord ++ tailWord_357859) baseStart_357859 baseEnd_357859 := by
    simpa [prefixWord, tailWord_357859, baseEnd_357859] using wordTrace_append hprefix tailTrace_357859
  have hstable : (prefixWord ++ tailWord_357859).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357859).length < 2 ^ (prefixWord ++ tailWord_357859).sum := by decide
  have hdescent : baseEnd_357859 < baseStart_357859 := by decide
  rcases family_descends (prefixWord ++ tailWord_357859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357878 : List Nat := [5, 1, 1, 1, 2, 9]
def baseStart_357878 : Nat := 118140960795 + 357878 * 2 ^ 59
def prefixEnd_357878 : Nat := 4983230072969 + 3 ^ 40 * 357878 * 2
def baseEnd_357878 : Nat := 12099649690196282099039

theorem tailTrace_357878 : CollatzResearch.WordTrace tailWord_357878 prefixEnd_357878 12099649690196282099039 := by
  unfold tailWord_357878
  simp only [CollatzResearch.WordTrace]
  refine ⟨815805187342287596340143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8701921998317734360961525 815805187342287596340143)
  ·
    refine ⟨1223707781013431394510215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 815805187342287596340143 1223707781013431394510215)
    ·
      refine ⟨1835561671520147091765323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1223707781013431394510215 1835561671520147091765323)
      ·
        refine ⟨2753342507280220637647985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835561671520147091765323 2753342507280220637647985)
        ·
          refine ⟨2065006880460165478235989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2753342507280220637647985 2065006880460165478235989)
          ·
            refine ⟨12099649690196282099039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2065006880460165478235989 12099649690196282099039)
            ·
              rfl

theorem cell19_357878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 9].length) (baseStart_357878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357878 prefixEnd_357878 := by exact prefixLift 357878
  have htrace : WordTrace (prefixWord ++ tailWord_357878) baseStart_357878 baseEnd_357878 := by
    simpa [prefixWord, tailWord_357878, baseEnd_357878] using wordTrace_append hprefix tailTrace_357878
  have hstable : (prefixWord ++ tailWord_357878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357878).length < 2 ^ (prefixWord ++ tailWord_357878).sum := by decide
  have hdescent : baseEnd_357878 < baseStart_357878 := by decide
  rcases family_descends (prefixWord ++ tailWord_357878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357880 : List Nat := [2, 1, 2, 1, 1, 12]
def baseStart_357880 : Nat := 118140960795 + 357880 * 2 ^ 59
def prefixEnd_357880 : Nat := 4983230072969 + 3 ^ 40 * 357880 * 2
def baseEnd_357880 : Nat := 12099717309047902982989

theorem tailTrace_357880 : CollatzResearch.WordTrace tailWord_357880 prefixEnd_357880 12099717309047902982989 := by
  unfold tailWord_357880
  simp only [CollatzResearch.WordTrace]
  refine ⟨6526477971734677941507547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8701970628979570588676729 6526477971734677941507547)
  ·
    refine ⟨9789716957602016912261321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6526477971734677941507547 9789716957602016912261321)
    ·
      refine ⟨7342287718201512684195991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9789716957602016912261321 7342287718201512684195991)
      ·
        refine ⟨11013431577302269026293987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7342287718201512684195991 11013431577302269026293987)
        ·
          refine ⟨16520147365953403539440981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11013431577302269026293987 16520147365953403539440981)
          ·
            refine ⟨12099717309047902982989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16520147365953403539440981 12099717309047902982989)
            ·
              rfl

theorem cell19_357880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 12].length) (baseStart_357880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357880 prefixEnd_357880 := by exact prefixLift 357880
  have htrace : WordTrace (prefixWord ++ tailWord_357880) baseStart_357880 baseEnd_357880 := by
    simpa [prefixWord, tailWord_357880, baseEnd_357880] using wordTrace_append hprefix tailTrace_357880
  have hstable : (prefixWord ++ tailWord_357880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357880).length < 2 ^ (prefixWord ++ tailWord_357880).sum := by decide
  have hdescent : baseEnd_357880 < baseStart_357880 := by decide
  rcases family_descends (prefixWord ++ tailWord_357880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357895 : List Nat := [1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_357895 : Nat := 118140960795 + 357895 * 2 ^ 59
def prefixEnd_357895 : Nat := 4983230072969 + 3 ^ 40 * 357895 * 2
def baseEnd_357895 : Nat := 108902020053915536513527

theorem tailTrace_357895 : CollatzResearch.WordTrace tailWord_357895 prefixEnd_357895 108902020053915536513527 := by
  unfold tailWord_357895
  simp only [CollatzResearch.WordTrace]
  refine ⟨13053503038415013444811139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8702335358943342296540759 13053503038415013444811139)
  ·
    refine ⟨19580254557622520167216709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13053503038415013444811139 19580254557622520167216709)
    ·
      refine ⟨3671297729554222531353133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19580254557622520167216709 3671297729554222531353133)
      ·
        refine ⟨1376736648582833449257425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3671297729554222531353133 1376736648582833449257425)
        ·
          refine ⟨1032552486437125086943069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1376736648582833449257425 1032552486437125086943069)
          ·
            refine ⟨387207182413921907603651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1032552486437125086943069 387207182413921907603651)
            ·
              refine ⟨580810773620882861405477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387207182413921907603651 580810773620882861405477)
              ·
                refine ⟨108902020053915536513527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 580810773620882861405477 108902020053915536513527)
                ·
                  rfl

theorem cell19_357895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_357895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357895 prefixEnd_357895 := by exact prefixLift 357895
  have htrace : WordTrace (prefixWord ++ tailWord_357895) baseStart_357895 baseEnd_357895 := by
    simpa [prefixWord, tailWord_357895, baseEnd_357895] using wordTrace_append hprefix tailTrace_357895
  have hstable : (prefixWord ++ tailWord_357895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357895).length < 2 ^ (prefixWord ++ tailWord_357895).sum := by decide
  have hdescent : baseEnd_357895 < baseStart_357895 := by decide
  rcases family_descends (prefixWord ++ tailWord_357895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_357992 : List Nat := [2, 1, 4, 3, 1, 1, 7]
def baseStart_357992 : Nat := 118140960795 + 357992 * 2 ^ 59
def prefixEnd_357992 : Nat := 4983230072969 + 3 ^ 40 * 357992 * 2
def baseEnd_357992 : Nat := 36310511894216017452569

theorem tailTrace_357992 : CollatzResearch.WordTrace tailWord_357992 prefixEnd_357992 36310511894216017452569 := by
  unfold tailWord_357992
  simp only [CollatzResearch.WordTrace]
  refine ⟨6528520459531799505546115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8704693946042399340728153 6528520459531799505546115)
  ·
    refine ⟨9792780689297699258319173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6528520459531799505546115 9792780689297699258319173)
    ·
      refine ⟨1836146379243318610934845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9792780689297699258319173 1836146379243318610934845)
      ·
        refine ⟨688554892216244479100567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1836146379243318610934845 688554892216244479100567)
        ·
          refine ⟨1032832338324366718650851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688554892216244479100567 1032832338324366718650851)
          ·
            refine ⟨1549248507486550077976277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032832338324366718650851 1549248507486550077976277)
            ·
              refine ⟨36310511894216017452569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1549248507486550077976277 36310511894216017452569)
              ·
                rfl

theorem cell19_357992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_357992 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_357992 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_357992 prefixEnd_357992 := by exact prefixLift 357992
  have htrace : WordTrace (prefixWord ++ tailWord_357992) baseStart_357992 baseEnd_357992 := by
    simpa [prefixWord, tailWord_357992, baseEnd_357992] using wordTrace_append hprefix tailTrace_357992
  have hstable : (prefixWord ++ tailWord_357992).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_357992).length < 2 ^ (prefixWord ++ tailWord_357992).sum := by decide
  have hdescent : baseEnd_357992 < baseStart_357992 := by decide
  rcases family_descends (prefixWord ++ tailWord_357992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358030 : List Nat := [4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_358030 : Nat := 118140960795 + 358030 * 2 ^ 59
def prefixEnd_358030 : Nat := 4983230072969 + 3 ^ 40 * 358030 * 2
def baseEnd_358030 : Nat := 108943098506275223513159

theorem tailTrace_358030 : CollatzResearch.WordTrace tailWord_358030 prefixEnd_358030 108943098506275223513159 := by
  unfold tailWord_358030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632303361615741437621943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8705617928617287667317029 1632303361615741437621943)
  ·
    refine ⟨2448455042423612156432915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1632303361615741437621943 2448455042423612156432915)
    ·
      refine ⟨3672682563635418234649373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2448455042423612156432915 3672682563635418234649373)
      ·
        refine ⟨1377255961363281837993515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3672682563635418234649373 1377255961363281837993515)
        ·
          refine ⟨2065883942044922756990273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377255961363281837993515 2065883942044922756990273)
          ·
            refine ⟨1549412956533692067742705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2065883942044922756990273 1549412956533692067742705)
            ·
              refine ⟨1162059717400269050807029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549412956533692067742705 1162059717400269050807029)
              ·
                refine ⟨108943098506275223513159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1162059717400269050807029 108943098506275223513159)
                ·
                  rfl

theorem cell19_358030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_358030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358030 prefixEnd_358030 := by exact prefixLift 358030
  have htrace : WordTrace (prefixWord ++ tailWord_358030) baseStart_358030 baseEnd_358030 := by
    simpa [prefixWord, tailWord_358030, baseEnd_358030] using wordTrace_append hprefix tailTrace_358030
  have hstable : (prefixWord ++ tailWord_358030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358030).length < 2 ^ (prefixWord ++ tailWord_358030).sum := by decide
  have hdescent : baseEnd_358030 < baseStart_358030 := by decide
  rcases family_descends (prefixWord ++ tailWord_358030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358047 : List Nat := [1, 1, 2, 7, 2, 6]
def baseStart_358047 : Nat := 118140960795 + 358047 * 2 ^ 59
def prefixEnd_358047 : Nat := 4983230072969 + 3 ^ 40 * 358047 * 2
def baseEnd_358047 : Nat := 12105363483158246792815

theorem tailTrace_358047 : CollatzResearch.WordTrace tailWord_358047 prefixEnd_358047 12105363483158246792815 := by
  unfold tailWord_358047
  simp only [CollatzResearch.WordTrace]
  refine ⟨13059046933864343404344395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8706031289242895602896263 13059046933864343404344395)
  ·
    refine ⟨19588570400796515106516593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13059046933864343404344395 19588570400796515106516593)
    ·
      refine ⟨14691427800597386329887445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19588570400796515106516593 14691427800597386329887445)
      ·
        refine ⟨344330339076501242106737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14691427800597386329887445 344330339076501242106737)
        ·
          refine ⟨258247754307375931580053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344330339076501242106737 258247754307375931580053)
          ·
            refine ⟨12105363483158246792815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 258247754307375931580053 12105363483158246792815)
            ·
              rfl

theorem cell19_358047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 6].length) (baseStart_358047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358047 prefixEnd_358047 := by exact prefixLift 358047
  have htrace : WordTrace (prefixWord ++ tailWord_358047) baseStart_358047 baseEnd_358047 := by
    simpa [prefixWord, tailWord_358047, baseEnd_358047] using wordTrace_append hprefix tailTrace_358047
  have hstable : (prefixWord ++ tailWord_358047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358047).length < 2 ^ (prefixWord ++ tailWord_358047).sum := by decide
  have hdescent : baseEnd_358047 < baseStart_358047 := by decide
  rcases family_descends (prefixWord ++ tailWord_358047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358062 : List Nat := [4, 1, 4, 1, 3, 1, 1, 4]
def baseStart_358062 : Nat := 118140960795 + 358062 * 2 ^ 59
def prefixEnd_358062 : Nat := 4983230072969 + 3 ^ 40 * 358062 * 2
def baseEnd_358062 : Nat := 108952835620908630801961

theorem tailTrace_358062 : CollatzResearch.WordTrace tailWord_358062 prefixEnd_358062 108952835620908630801961 := by
  unfold tailWord_358062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632449253601250120767555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8706396019206667310760293 1632449253601250120767555)
  ·
    refine ⟨2448673880401875181151333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1632449253601250120767555 2448673880401875181151333)
    ·
      refine ⟨459126352575351596465875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2448673880401875181151333 459126352575351596465875)
      ·
        refine ⟨688689528863027394698813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459126352575351596465875 688689528863027394698813)
        ·
          refine ⟨258258573323635273012055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 688689528863027394698813 258258573323635273012055)
          ·
            refine ⟨387387859985452909518083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258258573323635273012055 387387859985452909518083)
            ·
              refine ⟨581081789978179364277125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387387859985452909518083 581081789978179364277125)
              ·
                refine ⟨108952835620908630801961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 581081789978179364277125 108952835620908630801961)
                ·
                  rfl

theorem cell19_358062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_358062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358062 prefixEnd_358062 := by exact prefixLift 358062
  have htrace : WordTrace (prefixWord ++ tailWord_358062) baseStart_358062 baseEnd_358062 := by
    simpa [prefixWord, tailWord_358062, baseEnd_358062] using wordTrace_append hprefix tailTrace_358062
  have hstable : (prefixWord ++ tailWord_358062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358062).length < 2 ^ (prefixWord ++ tailWord_358062).sum := by decide
  have hdescent : baseEnd_358062 < baseStart_358062 := by decide
  rcases family_descends (prefixWord ++ tailWord_358062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358087 : List Nat := [1, 1, 4, 1, 1, 1, 7, 3]
def baseStart_358087 : Nat := 118140960795 + 358087 * 2 ^ 59
def prefixEnd_358087 : Nat := 4983230072969 + 3 ^ 40 * 358087 * 2
def baseEnd_358087 : Nat := 108960442741715980246337

theorem tailTrace_358087 : CollatzResearch.WordTrace tailWord_358087 prefixEnd_358087 108960442741715980246337 := by
  unfold tailWord_358087
  simp only [CollatzResearch.WordTrace]
  refine ⟨13060505853719430235800515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8707003902479620157200343 13060505853719430235800515)
  ·
    refine ⟨19590758780579145353700773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13060505853719430235800515 19590758780579145353700773)
    ·
      refine ⟨3673267271358589753818895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19590758780579145353700773 3673267271358589753818895)
      ·
        refine ⟨5509900907037884630728343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3673267271358589753818895 5509900907037884630728343)
        ·
          refine ⟨8264851360556826946092515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5509900907037884630728343 8264851360556826946092515)
          ·
            refine ⟨12397277040835240419138773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8264851360556826946092515 12397277040835240419138773)
            ·
              refine ⟨290561180644575947323565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12397277040835240419138773 290561180644575947323565)
              ·
                refine ⟨108960442741715980246337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290561180644575947323565 108960442741715980246337)
                ·
                  rfl

theorem cell19_358087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_358087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358087 prefixEnd_358087 := by exact prefixLift 358087
  have htrace : WordTrace (prefixWord ++ tailWord_358087) baseStart_358087 baseEnd_358087 := by
    simpa [prefixWord, tailWord_358087, baseEnd_358087] using wordTrace_append hprefix tailTrace_358087
  have hstable : (prefixWord ++ tailWord_358087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358087).length < 2 ^ (prefixWord ++ tailWord_358087).sum := by decide
  have hdescent : baseEnd_358087 < baseStart_358087 := by decide
  rcases family_descends (prefixWord ++ tailWord_358087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358102 : List Nat := [5, 2, 1, 3, 1, 1, 6]
def baseStart_358102 : Nat := 118140960795 + 358102 * 2 ^ 59
def prefixEnd_358102 : Nat := 4983230072969 + 3 ^ 40 * 358102 * 2
def baseEnd_358102 : Nat := 36321669004733463304321

theorem tailTrace_358102 : CollatzResearch.WordTrace tailWord_358102 prefixEnd_358102 36321669004733463304321 := by
  unfold tailWord_358102
  simp only [CollatzResearch.WordTrace]
  refine ⟨816315809291567987349785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8707368632443391865064373 816315809291567987349785)
  ·
    refine ⟨612236856968675990512339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 816315809291567987349785 612236856968675990512339)
    ·
      refine ⟨918355285453013985768509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612236856968675990512339 918355285453013985768509)
      ·
        refine ⟨344383232044880244663191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 918355285453013985768509 344383232044880244663191)
        ·
          refine ⟨516574848067320366994787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344383232044880244663191 516574848067320366994787)
          ·
            refine ⟨774862272100980550492181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516574848067320366994787 774862272100980550492181)
            ·
              refine ⟨36321669004733463304321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 774862272100980550492181 36321669004733463304321)
              ·
                rfl

theorem cell19_358102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_358102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358102 prefixEnd_358102 := by exact prefixLift 358102
  have htrace : WordTrace (prefixWord ++ tailWord_358102) baseStart_358102 baseEnd_358102 := by
    simpa [prefixWord, tailWord_358102, baseEnd_358102] using wordTrace_append hprefix tailTrace_358102
  have hstable : (prefixWord ++ tailWord_358102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358102).length < 2 ^ (prefixWord ++ tailWord_358102).sum := by decide
  have hdescent : baseEnd_358102 < baseStart_358102 := by decide
  rcases family_descends (prefixWord ++ tailWord_358102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358127 : List Nat := [1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_358127 : Nat := 118140960795 + 358127 * 2 ^ 59
def prefixEnd_358127 : Nat := 4983230072969 + 3 ^ 40 * 358127 * 2
def baseEnd_358127 : Nat := 108972614135007739357339

theorem tailTrace_358127 : CollatzResearch.WordTrace tailWord_358127 prefixEnd_358127 108972614135007739357339 := by
  unfold tailWord_358127
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061964773574517067256635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8707976515716344711504423 13061964773574517067256635)
  ·
    refine ⟨19592947160361775600884953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13061964773574517067256635 19592947160361775600884953)
    ·
      refine ⟨14694710370271331700663715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19592947160361775600884953 14694710370271331700663715)
      ·
        refine ⟨22042065555406997550995573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14694710370271331700663715 22042065555406997550995573)
        ·
          refine ⟨2066443645819406020405835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22042065555406997550995573 2066443645819406020405835)
          ·
            refine ⟨3099665468729109030608753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066443645819406020405835 3099665468729109030608753)
            ·
              refine ⟨2324749101546831772956565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3099665468729109030608753 2324749101546831772956565)
              ·
                refine ⟨108972614135007739357339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2324749101546831772956565 108972614135007739357339)
                ·
                  rfl

theorem cell19_358127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_358127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358127 prefixEnd_358127 := by exact prefixLift 358127
  have htrace : WordTrace (prefixWord ++ tailWord_358127) baseStart_358127 baseEnd_358127 := by
    simpa [prefixWord, tailWord_358127, baseEnd_358127] using wordTrace_append hprefix tailTrace_358127
  have hstable : (prefixWord ++ tailWord_358127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358127).length < 2 ^ (prefixWord ++ tailWord_358127).sum := by decide
  have hdescent : baseEnd_358127 < baseStart_358127 := by decide
  rcases family_descends (prefixWord ++ tailWord_358127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358142 : List Nat := [4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_358142 : Nat := 118140960795 + 358142 * 2 ^ 59
def prefixEnd_358142 : Nat := 4983230072969 + 3 ^ 40 * 358142 * 2
def baseEnd_358142 : Nat := 108977178407492149023965

theorem tailTrace_358142 : CollatzResearch.WordTrace tailWord_358142 prefixEnd_358142 108977178407492149023965 := by
  unfold tailWord_358142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632813983565021828631585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8708341245680116419368453 1632813983565021828631585)
  ·
    refine ⟨1224610487673766371473689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1632813983565021828631585 1224610487673766371473689)
    ·
      refine ⟨918457865755324778605267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1224610487673766371473689 918457865755324778605267)
      ·
        refine ⟨1377686798632987167907901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918457865755324778605267 1377686798632987167907901)
        ·
          refine ⟨516632549487370187965463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1377686798632987167907901 516632549487370187965463)
          ·
            refine ⟨774948824231055281948195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516632549487370187965463 774948824231055281948195)
            ·
              refine ⟨1162423236346582922922293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774948824231055281948195 1162423236346582922922293)
              ·
                refine ⟨108977178407492149023965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1162423236346582922922293 108977178407492149023965)
                ·
                  rfl

theorem cell19_358142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_358142 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358142 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358142 prefixEnd_358142 := by exact prefixLift 358142
  have htrace : WordTrace (prefixWord ++ tailWord_358142) baseStart_358142 baseEnd_358142 := by
    simpa [prefixWord, tailWord_358142, baseEnd_358142] using wordTrace_append hprefix tailTrace_358142
  have hstable : (prefixWord ++ tailWord_358142).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358142).length < 2 ^ (prefixWord ++ tailWord_358142).sum := by decide
  have hdescent : baseEnd_358142 < baseStart_358142 := by decide
  rcases family_descends (prefixWord ++ tailWord_358142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358165 : List Nat := [1, 3, 2, 1, 2, 3, 7]
def baseStart_358165 : Nat := 118140960795 + 358165 * 2 ^ 59
def prefixEnd_358165 : Nat := 4983230072969 + 3 ^ 40 * 358165 * 2
def baseEnd_358165 : Nat := 36328058986211636837597

theorem tailTrace_358165 : CollatzResearch.WordTrace tailWord_358165 prefixEnd_358165 36328058986211636837597 := by
  unfold tailWord_358165
  simp only [CollatzResearch.WordTrace]
  refine ⟨13063350747436849557139949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8708900498291233038093299 13063350747436849557139949)
  ·
    refine ⟨4898756530288818583927481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13063350747436849557139949 4898756530288818583927481)
    ·
      refine ⟨3674067397716613937945611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4898756530288818583927481 3674067397716613937945611)
      ·
        refine ⟨5511101096574920906918417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3674067397716613937945611 5511101096574920906918417)
        ·
          refine ⟨4133325822431190680188813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5511101096574920906918417 4133325822431190680188813)
          ·
            refine ⟨1549997183411696505070805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4133325822431190680188813 1549997183411696505070805)
            ·
              refine ⟨36328058986211636837597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1549997183411696505070805 36328058986211636837597)
              ·
                rfl

theorem cell19_358165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_358165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358165 prefixEnd_358165 := by exact prefixLift 358165
  have htrace : WordTrace (prefixWord ++ tailWord_358165) baseStart_358165 baseEnd_358165 := by
    simpa [prefixWord, tailWord_358165, baseEnd_358165] using wordTrace_append hprefix tailTrace_358165
  have hstable : (prefixWord ++ tailWord_358165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358165).length < 2 ^ (prefixWord ++ tailWord_358165).sum := by decide
  have hdescent : baseEnd_358165 < baseStart_358165 := by decide
  rcases family_descends (prefixWord ++ tailWord_358165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358220 : List Nat := [2, 2, 1, 3, 5, 6]
def baseStart_358220 : Nat := 118140960795 + 358220 * 2 ^ 59
def prefixEnd_358220 : Nat := 4983230072969 + 3 ^ 40 * 358220 * 2
def baseEnd_358220 : Nat := 12111212513823453254491

theorem tailTrace_358220 : CollatzResearch.WordTrace tailWord_358220 prefixEnd_358220 12111212513823453254491 := by
  unfold tailWord_358220
  simp only [CollatzResearch.WordTrace]
  refine ⟨6532678381118796975196057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8710237841491729300261409 6532678381118796975196057)
  ·
    refine ⟨4899508785839097731397043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6532678381118796975196057 4899508785839097731397043)
    ·
      refine ⟨7349263178758646597095565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4899508785839097731397043 7349263178758646597095565)
      ·
        refine ⟨2755973692034492473910837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7349263178758646597095565 2755973692034492473910837)
        ·
          refine ⟨258372533628233669429141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2755973692034492473910837 258372533628233669429141)
          ·
            refine ⟨12111212513823453254491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 258372533628233669429141 12111212513823453254491)
            ·
              rfl

theorem cell19_358220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 6].length) (baseStart_358220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358220 prefixEnd_358220 := by exact prefixLift 358220
  have htrace : WordTrace (prefixWord ++ tailWord_358220) baseStart_358220 baseEnd_358220 := by
    simpa [prefixWord, tailWord_358220, baseEnd_358220] using wordTrace_append hprefix tailTrace_358220
  have hstable : (prefixWord ++ tailWord_358220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358220).length < 2 ^ (prefixWord ++ tailWord_358220).sum := by decide
  have hdescent : baseEnd_358220 < baseStart_358220 := by decide
  rcases family_descends (prefixWord ++ tailWord_358220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358239 : List Nat := [1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_358239 : Nat := 118140960795 + 358239 * 2 ^ 59
def prefixEnd_358239 : Nat := 4983230072969 + 3 ^ 40 * 358239 * 2
def baseEnd_358239 : Nat := 109006694036224664868145

theorem tailTrace_358239 : CollatzResearch.WordTrace tailWord_358239 prefixEnd_358239 109006694036224664868145 := by
  unfold tailWord_358239
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066049749168760195333771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8710699832779173463555847 13066049749168760195333771)
  ·
    refine ⟨19599074623753140293000657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13066049749168760195333771 19599074623753140293000657)
    ·
      refine ⟨14699305967814855219750493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19599074623753140293000657 14699305967814855219750493)
      ·
        refine ⟨5512239737930570707406435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14699305967814855219750493 5512239737930570707406435)
        ·
          refine ⟨8268359606895856061109653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5512239737930570707406435 8268359606895856061109653)
          ·
            refine ⟨387579356573243252864515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8268359606895856061109653 387579356573243252864515)
            ·
              refine ⟨581369034859864879296773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 387579356573243252864515 581369034859864879296773)
              ·
                refine ⟨109006694036224664868145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 581369034859864879296773 109006694036224664868145)
                ·
                  rfl

theorem cell19_358239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_358239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358239 prefixEnd_358239 := by exact prefixLift 358239
  have htrace : WordTrace (prefixWord ++ tailWord_358239) baseStart_358239 baseEnd_358239 := by
    simpa [prefixWord, tailWord_358239, baseEnd_358239] using wordTrace_append hprefix tailTrace_358239
  have hstable : (prefixWord ++ tailWord_358239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358239).length < 2 ^ (prefixWord ++ tailWord_358239).sum := by decide
  have hdescent : baseEnd_358239 < baseStart_358239 := by decide
  rcases family_descends (prefixWord ++ tailWord_358239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358332 : List Nat := [2, 2, 2, 5, 1, 2, 5]
def baseStart_358332 : Nat := 118140960795 + 358332 * 2 ^ 59
def prefixEnd_358332 : Nat := 4983230072969 + 3 ^ 40 * 358332 * 2
def baseEnd_358332 : Nat := 36344997508542668267075

theorem tailTrace_358332 : CollatzResearch.WordTrace tailWord_358332 prefixEnd_358332 36344997508542668267075 := by
  unfold tailWord_358332
  simp only [CollatzResearch.WordTrace]
  refine ⟨6534720868915918539234625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8712961158554558052312833 6534720868915918539234625)
  ·
    refine ⟨4901040651686938904425969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6534720868915918539234625 4901040651686938904425969)
    ·
      refine ⟨3675780488765204178319477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4901040651686938904425969 3675780488765204178319477)
      ·
        refine ⟨344604420821737891717451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3675780488765204178319477 344604420821737891717451)
        ·
          refine ⟨516906631232606837576177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344604420821737891717451 516906631232606837576177)
          ·
            refine ⟨387679973424455128182133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516906631232606837576177 387679973424455128182133)
            ·
              refine ⟨36344997508542668267075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 387679973424455128182133 36344997508542668267075)
              ·
                rfl

theorem cell19_358332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_358332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358332 prefixEnd_358332 := by exact prefixLift 358332
  have htrace : WordTrace (prefixWord ++ tailWord_358332) baseStart_358332 baseEnd_358332 := by
    simpa [prefixWord, tailWord_358332, baseEnd_358332] using wordTrace_append hprefix tailTrace_358332
  have hstable : (prefixWord ++ tailWord_358332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358332).length < 2 ^ (prefixWord ++ tailWord_358332).sum := by decide
  have hdescent : baseEnd_358332 < baseStart_358332 := by decide
  rcases family_descends (prefixWord ++ tailWord_358332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358334 : List Nat := [4, 2, 1, 1, 1, 5, 5]
def baseStart_358334 : Nat := 118140960795 + 358334 * 2 ^ 59
def prefixEnd_358334 : Nat := 4983230072969 + 3 ^ 40 * 358334 * 2
def baseEnd_358334 : Nat := 36345200365097530918925

theorem tailTrace_358334 : CollatzResearch.WordTrace tailWord_358334 prefixEnd_358334 36345200365097530918925 := by
  unfold tailWord_358334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633689335478073927505257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8713009789216394280028037 1633689335478073927505257)
  ·
    refine ⟨1225267001608555445628943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1633689335478073927505257 1225267001608555445628943)
    ·
      refine ⟨1837900502412833168443415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1225267001608555445628943 1837900502412833168443415)
      ·
        refine ⟨2756850753619249752665123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837900502412833168443415 2756850753619249752665123)
        ·
          refine ⟨4135276130428874628997685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2756850753619249752665123 4135276130428874628997685)
          ·
            refine ⟨387682137227706996468533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4135276130428874628997685 387682137227706996468533)
            ·
              refine ⟨36345200365097530918925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 387682137227706996468533 36345200365097530918925)
              ·
                rfl

theorem cell19_358334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_358334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358334 prefixEnd_358334 := by exact prefixLift 358334
  have htrace : WordTrace (prefixWord ++ tailWord_358334) baseStart_358334 baseEnd_358334 := by
    simpa [prefixWord, tailWord_358334, baseEnd_358334] using wordTrace_append hprefix tailTrace_358334
  have hstable : (prefixWord ++ tailWord_358334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358334).length < 2 ^ (prefixWord ++ tailWord_358334).sum := by decide
  have hdescent : baseEnd_358334 < baseStart_358334 := by decide
  rcases family_descends (prefixWord ++ tailWord_358334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358450 : List Nat := [3, 2, 1, 1, 2, 4, 6]
def baseStart_358450 : Nat := 118140960795 + 358450 * 2 ^ 59
def prefixEnd_358450 : Nat := 4983230072969 + 3 ^ 40 * 358450 * 2
def baseEnd_358450 : Nat := 36356966045279564726227

theorem tailTrace_358450 : CollatzResearch.WordTrace tailWord_358450 prefixEnd_358450 36356966045279564726227 := by
  unfold tailWord_358450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3268436387851085807816201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8715830367602895487509869 3268436387851085807816201)
  ·
    refine ⟨2451327290888314355862151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3268436387851085807816201 2451327290888314355862151)
    ·
      refine ⟨3676990936332471533793227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451327290888314355862151 3676990936332471533793227)
      ·
        refine ⟨5515486404498707300689841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3676990936332471533793227 5515486404498707300689841)
        ·
          refine ⟨4136614803374030475517381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5515486404498707300689841 4136614803374030475517381)
          ·
            refine ⟨775615275632630714159509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4136614803374030475517381 775615275632630714159509)
            ·
              refine ⟨36356966045279564726227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 775615275632630714159509 36356966045279564726227)
              ·
                rfl

theorem cell19_358450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_358450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358450 prefixEnd_358450 := by exact prefixLift 358450
  have htrace : WordTrace (prefixWord ++ tailWord_358450) baseStart_358450 baseEnd_358450 := by
    simpa [prefixWord, tailWord_358450, baseEnd_358450] using wordTrace_append hprefix tailTrace_358450
  have hstable : (prefixWord ++ tailWord_358450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358450).length < 2 ^ (prefixWord ++ tailWord_358450).sum := by decide
  have hdescent : baseEnd_358450 < baseStart_358450 := by decide
  rcases family_descends (prefixWord ++ tailWord_358450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358482 : List Nat := [3, 2, 2, 1, 5, 1, 2, 3]
def baseStart_358482 : Nat := 118140960795 + 358482 * 2 ^ 59
def prefixEnd_358482 : Nat := 4983230072969 + 3 ^ 40 * 358482 * 2
def baseEnd_358482 : Nat := 109080635250472101467483

theorem tailTrace_358482 : CollatzResearch.WordTrace tailWord_358482 prefixEnd_358482 109080635250472101467483 := by
  unfold tailWord_358482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3268728171822103174107425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8716608458192275130953133 3268728171822103174107425)
  ·
    refine ⟨2451546128866577380580569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3268728171822103174107425 2451546128866577380580569)
    ·
      refine ⟨1838659596649933035435427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2451546128866577380580569 1838659596649933035435427)
      ·
        refine ⟨2757989394974899553153141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838659596649933035435427 2757989394974899553153141)
        ·
          refine ⟨258561505778896833108107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2757989394974899553153141 258561505778896833108107)
          ·
            refine ⟨387842258668345249662161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258561505778896833108107 387842258668345249662161)
            ·
              refine ⟨290881694001258937246621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387842258668345249662161 290881694001258937246621)
              ·
                refine ⟨109080635250472101467483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290881694001258937246621 109080635250472101467483)
                ·
                  rfl

theorem cell19_358482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_358482 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358482 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358482 prefixEnd_358482 := by exact prefixLift 358482
  have htrace : WordTrace (prefixWord ++ tailWord_358482) baseStart_358482 baseEnd_358482 := by
    simpa [prefixWord, tailWord_358482, baseEnd_358482] using wordTrace_append hprefix tailTrace_358482
  have hstable : (prefixWord ++ tailWord_358482).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358482).length < 2 ^ (prefixWord ++ tailWord_358482).sum := by decide
  have hdescent : baseEnd_358482 < baseStart_358482 := by decide
  rcases family_descends (prefixWord ++ tailWord_358482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358488 : List Nat := [2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_358488 : Nat := 118140960795 + 358488 * 2 ^ 59
def prefixEnd_358488 : Nat := 4983230072969 + 3 ^ 40 * 358488 * 2
def baseEnd_358488 : Nat := 109082460959465865334133

theorem tailTrace_358488 : CollatzResearch.WordTrace tailWord_358488 prefixEnd_358488 109082460959465865334133 := by
  unfold tailWord_358488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6537565762633337860574059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8716754350177783814098745 6537565762633337860574059)
  ·
    refine ⟨9806348643950006790861089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6537565762633337860574059 9806348643950006790861089)
    ·
      refine ⟨7354761482962505093145817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9806348643950006790861089 7354761482962505093145817)
      ·
        refine ⟨5516071112221878819859363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7354761482962505093145817 5516071112221878819859363)
        ·
          refine ⟨8274106668332818229789045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516071112221878819859363 8274106668332818229789045)
          ·
            refine ⟨775697500156201709042723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8274106668332818229789045 775697500156201709042723)
            ·
              refine ⟨1163546250234302563564085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775697500156201709042723 1163546250234302563564085)
              ·
                refine ⟨109082460959465865334133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1163546250234302563564085 109082460959465865334133)
                ·
                  rfl

theorem cell19_358488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_358488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358488 prefixEnd_358488 := by exact prefixLift 358488
  have htrace : WordTrace (prefixWord ++ tailWord_358488) baseStart_358488 baseEnd_358488 := by
    simpa [prefixWord, tailWord_358488, baseEnd_358488] using wordTrace_append hprefix tailTrace_358488
  have hstable : (prefixWord ++ tailWord_358488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358488).length < 2 ^ (prefixWord ++ tailWord_358488).sum := by decide
  have hdescent : baseEnd_358488 < baseStart_358488 := by decide
  rcases family_descends (prefixWord ++ tailWord_358488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358564 : List Nat := [2, 3, 1, 2, 4, 7]
def baseStart_358564 : Nat := 118140960795 + 358564 * 2 ^ 59
def prefixEnd_358564 : Nat := 4983230072969 + 3 ^ 40 * 358564 * 2
def baseEnd_358564 : Nat := 12122842956302245293893

theorem tailTrace_358564 : CollatzResearch.WordTrace tailWord_358564 prefixEnd_358564 12122842956302245293893 := by
  unfold tailWord_358564
  simp only [CollatzResearch.WordTrace]
  refine ⟨6538951736495670350457373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8718602315327560467276497 6538951736495670350457373)
  ·
    refine ⟨2452106901185876381421515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6538951736495670350457373 2452106901185876381421515)
    ·
      refine ⟨3678160351778814572132273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2452106901185876381421515 3678160351778814572132273)
      ·
        refine ⟨2758620263834110929099205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3678160351778814572132273 2758620263834110929099205)
        ·
          refine ⟨517241299468895799206101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2758620263834110929099205 517241299468895799206101)
          ·
            refine ⟨12122842956302245293893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 517241299468895799206101 12122842956302245293893)
            ·
              rfl

theorem cell19_358564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 7].length) (baseStart_358564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358564 prefixEnd_358564 := by exact prefixLift 358564
  have htrace : WordTrace (prefixWord ++ tailWord_358564) baseStart_358564 baseEnd_358564 := by
    simpa [prefixWord, tailWord_358564, baseEnd_358564] using wordTrace_append hprefix tailTrace_358564
  have hstable : (prefixWord ++ tailWord_358564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358564).length < 2 ^ (prefixWord ++ tailWord_358564).sum := by decide
  have hdescent : baseEnd_358564 < baseStart_358564 := by decide
  rcases family_descends (prefixWord ++ tailWord_358564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358583 : List Nat := [1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_358583 : Nat := 118140960795 + 358583 * 2 ^ 59
def prefixEnd_358583 : Nat := 4983230072969 + 3 ^ 40 * 358583 * 2
def baseEnd_358583 : Nat := 109111368018533793222763

theorem tailTrace_358583 : CollatzResearch.WordTrace tailWord_358583 prefixEnd_358583 109111368018533793222763 := by
  unfold tailWord_358583
  simp only [CollatzResearch.WordTrace]
  refine ⟨13078596459922506945856403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8719064306615004630570935 13078596459922506945856403)
  ·
    refine ⟨19617894689883760418784605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13078596459922506945856403 19617894689883760418784605)
    ·
      refine ⟨7356710508706410157044227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19617894689883760418784605 7356710508706410157044227)
      ·
        refine ⟨11035065763059615235566341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7356710508706410157044227 11035065763059615235566341)
        ·
          refine ⟨2069074830573677856668689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11035065763059615235566341 2069074830573677856668689)
          ·
            refine ⟨1551806122930258392501517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2069074830573677856668689 1551806122930258392501517)
            ·
              refine ⟨581927296098846897188069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1551806122930258392501517 581927296098846897188069)
              ·
                refine ⟨109111368018533793222763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 581927296098846897188069 109111368018533793222763)
                ·
                  rfl

theorem cell19_358583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_358583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358583 prefixEnd_358583 := by exact prefixLift 358583
  have htrace : WordTrace (prefixWord ++ tailWord_358583) baseStart_358583 baseEnd_358583 := by
    simpa [prefixWord, tailWord_358583, baseEnd_358583] using wordTrace_append hprefix tailTrace_358583
  have hstable : (prefixWord ++ tailWord_358583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358583).length < 2 ^ (prefixWord ++ tailWord_358583).sum := by decide
  have hdescent : baseEnd_358583 < baseStart_358583 := by decide
  rcases family_descends (prefixWord ++ tailWord_358583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358737 : List Nat := [1, 2, 2, 1, 4, 9]
def baseStart_358737 : Nat := 118140960795 + 358737 * 2 ^ 59
def prefixEnd_358737 : Nat := 4983230072969 + 3 ^ 40 * 358737 * 2
def baseEnd_358737 : Nat := 12128691986967451755569

theorem tailTrace_358737 : CollatzResearch.WordTrace tailWord_358737 prefixEnd_358737 12128691986967451755569 := by
  unfold tailWord_358737
  simp only [CollatzResearch.WordTrace]
  refine ⟨13084213301364591246962465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8722808867576394164641643 13084213301364591246962465)
  ·
    refine ⟨9813159976023443435221849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13084213301364591246962465 9813159976023443435221849)
    ·
      refine ⟨7359869982017582576416387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9813159976023443435221849 7359869982017582576416387)
      ·
        refine ⟨11039804973026373864624581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7359869982017582576416387 11039804973026373864624581)
        ·
          refine ⟨2069963432442445099617109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11039804973026373864624581 2069963432442445099617109)
          ·
            refine ⟨12128691986967451755569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2069963432442445099617109 12128691986967451755569)
            ·
              rfl

theorem cell19_358737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 9].length) (baseStart_358737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358737 prefixEnd_358737 := by exact prefixLift 358737
  have htrace : WordTrace (prefixWord ++ tailWord_358737) baseStart_358737 baseEnd_358737 := by
    simpa [prefixWord, tailWord_358737, baseEnd_358737] using wordTrace_append hprefix tailTrace_358737
  have hstable : (prefixWord ++ tailWord_358737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358737).length < 2 ^ (prefixWord ++ tailWord_358737).sum := by decide
  have hdescent : baseEnd_358737 < baseStart_358737 := by decide
  rcases family_descends (prefixWord ++ tailWord_358737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358748 : List Nat := [2, 2, 4, 3, 2, 1, 1, 4]
def baseStart_358748 : Nat := 118140960795 + 358748 * 2 ^ 59
def prefixEnd_358748 : Nat := 4983230072969 + 3 ^ 40 * 358748 * 2
def baseEnd_358748 : Nat := 109161575015862299555647

theorem tailTrace_358748 : CollatzResearch.WordTrace tailWord_358748 prefixEnd_358748 109161575015862299555647 := by
  unfold tailWord_358748
  simp only [CollatzResearch.WordTrace]
  refine ⟨6542307252162370062806449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8723076336216493417075265 6542307252162370062806449)
  ·
    refine ⟨4906730439121777547104837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6542307252162370062806449 4906730439121777547104837)
    ·
      refine ⟨920011957335333290082157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4906730439121777547104837 920011957335333290082157)
      ·
        refine ⟨345004484000749983780809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 920011957335333290082157 345004484000749983780809)
        ·
          refine ⟨258753363000562487835607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345004484000749983780809 258753363000562487835607)
          ·
            refine ⟨388130044500843731753411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258753363000562487835607 388130044500843731753411)
            ·
              refine ⟨582195066751265597630117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388130044500843731753411 582195066751265597630117)
              ·
                refine ⟨109161575015862299555647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582195066751265597630117 109161575015862299555647)
                ·
                  rfl

theorem cell19_358748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_358748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358748 prefixEnd_358748 := by exact prefixLift 358748
  have htrace : WordTrace (prefixWord ++ tailWord_358748) baseStart_358748 baseEnd_358748 := by
    simpa [prefixWord, tailWord_358748, baseEnd_358748] using wordTrace_append hprefix tailTrace_358748
  have hstable : (prefixWord ++ tailWord_358748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358748).length < 2 ^ (prefixWord ++ tailWord_358748).sum := by decide
  have hdescent : baseEnd_358748 < baseStart_358748 := by decide
  rcases family_descends (prefixWord ++ tailWord_358748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358752 : List Nat := [2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_358752 : Nat := 118140960795 + 358752 * 2 ^ 59
def prefixEnd_358752 : Nat := 4983230072969 + 3 ^ 40 * 358752 * 2
def baseEnd_358752 : Nat := 109162792155191475466747

theorem tailTrace_358752 : CollatzResearch.WordTrace tailWord_358752 prefixEnd_358752 109162792155191475466747 := by
  unfold tailWord_358752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6542380198155124404379255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8723173597540165872505673 6542380198155124404379255)
  ·
    refine ⟨9813570297232686606568883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6542380198155124404379255 9813570297232686606568883)
    ·
      refine ⟨14720355445849029909853325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9813570297232686606568883 14720355445849029909853325)
      ·
        refine ⟨5520133292193386216194997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14720355445849029909853325 5520133292193386216194997)
        ·
          refine ⟨517512496143129957768281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5520133292193386216194997 517512496143129957768281)
          ·
            refine ⟨388134372107347468326211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517512496143129957768281 388134372107347468326211)
            ·
              refine ⟨582201558161021202489317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388134372107347468326211 582201558161021202489317)
              ·
                refine ⟨109162792155191475466747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582201558161021202489317 109162792155191475466747)
                ·
                  rfl

theorem cell19_358752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_358752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358752 prefixEnd_358752 := by exact prefixLift 358752
  have htrace : WordTrace (prefixWord ++ tailWord_358752) baseStart_358752 baseEnd_358752 := by
    simpa [prefixWord, tailWord_358752, baseEnd_358752] using wordTrace_append hprefix tailTrace_358752
  have hstable : (prefixWord ++ tailWord_358752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358752).length < 2 ^ (prefixWord ++ tailWord_358752).sum := by decide
  have hdescent : baseEnd_358752 < baseStart_358752 := by decide
  rcases family_descends (prefixWord ++ tailWord_358752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358868 : List Nat := [2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_358868 : Nat := 118140960795 + 358868 * 2 ^ 59
def prefixEnd_358868 : Nat := 4983230072969 + 3 ^ 40 * 358868 * 2
def baseEnd_358868 : Nat := 109198089195737576888653

theorem tailTrace_358868 : CollatzResearch.WordTrace tailWord_358868 prefixEnd_358868 109198089195737576888653 := by
  unfold tailWord_358868
  simp only [CollatzResearch.WordTrace]
  refine ⟨6544495631945000309990629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8725994175926667079987505 6544495631945000309990629)
  ·
    refine ⟨1227092930989687558123243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6544495631945000309990629 1227092930989687558123243)
    ·
      refine ⟨1840639396484531337184865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1227092930989687558123243 1840639396484531337184865)
      ·
        refine ⟨1380479547363398502888649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1840639396484531337184865 1380479547363398502888649)
        ·
          refine ⟨1035359660522548877166487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1380479547363398502888649 1035359660522548877166487)
          ·
            refine ⟨1553039490783823315749731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035359660522548877166487 1553039490783823315749731)
            ·
              refine ⟨2329559236175734973624597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553039490783823315749731 2329559236175734973624597)
              ·
                refine ⟨109198089195737576888653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2329559236175734973624597 109198089195737576888653)
                ·
                  rfl

theorem cell19_358868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_358868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358868 prefixEnd_358868 := by exact prefixLift 358868
  have htrace : WordTrace (prefixWord ++ tailWord_358868) baseStart_358868 baseEnd_358868 := by
    simpa [prefixWord, tailWord_358868, baseEnd_358868] using wordTrace_append hprefix tailTrace_358868
  have hstable : (prefixWord ++ tailWord_358868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358868).length < 2 ^ (prefixWord ++ tailWord_358868).sum := by decide
  have hdescent : baseEnd_358868 < baseStart_358868 := by decide
  rcases family_descends (prefixWord ++ tailWord_358868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358965 : List Nat := [1, 3, 3, 1, 1, 2, 8]
def baseStart_358965 : Nat := 118140960795 + 358965 * 2 ^ 59
def prefixEnd_358965 : Nat := 4983230072969 + 3 ^ 40 * 358965 * 2
def baseEnd_358965 : Nat := 36409201608156697577611

theorem tailTrace_358965 : CollatzResearch.WordTrace tailWord_358965 prefixEnd_358965 36409201608156697577611 := by
  unfold tailWord_358965
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092529144538586186262349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8728352763025724124174899 13092529144538586186262349)
  ·
    refine ⟨4909698429201969819848381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13092529144538586186262349 4909698429201969819848381)
    ·
      refine ⟨1841136910950738682443143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4909698429201969819848381 1841136910950738682443143)
      ·
        refine ⟨2761705366426108023664715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841136910950738682443143 2761705366426108023664715)
        ·
          refine ⟨4142558049639162035497073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761705366426108023664715 4142558049639162035497073)
          ·
            refine ⟨3106918537229371526622805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4142558049639162035497073 3106918537229371526622805)
            ·
              refine ⟨36409201608156697577611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3106918537229371526622805 36409201608156697577611)
              ·
                rfl

theorem cell19_358965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_358965 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_358965 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_358965 prefixEnd_358965 := by exact prefixLift 358965
  have htrace : WordTrace (prefixWord ++ tailWord_358965) baseStart_358965 baseEnd_358965 := by
    simpa [prefixWord, tailWord_358965, baseEnd_358965] using wordTrace_append hprefix tailTrace_358965
  have hstable : (prefixWord ++ tailWord_358965).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358965).length < 2 ^ (prefixWord ++ tailWord_358965).sum := by decide
  have hdescent : baseEnd_358965 < baseStart_358965 := by decide
  rcases family_descends (prefixWord ++ tailWord_358965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359058 : List Nat := [3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_359058 : Nat := 118140960795 + 359058 * 2 ^ 59
def prefixEnd_359058 : Nat := 4983230072969 + 3 ^ 40 * 359058 * 2
def baseEnd_359058 : Nat := 109255903313873432665913

theorem tailTrace_359058 : CollatzResearch.WordTrace tailWord_359058 prefixEnd_359058 109255903313873432665913 := by
  unfold tailWord_359058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273980283300415767349457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8730614088801108712931885 3273980283300415767349457)
  ·
    refine ⟨2455485212475311825512093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3273980283300415767349457 2455485212475311825512093)
    ·
      refine ⟨920806954678241934567035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2455485212475311825512093 920806954678241934567035)
      ·
        refine ⟨1381210432017362901850553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920806954678241934567035 1381210432017362901850553)
        ·
          refine ⟨1035907824013022176387915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1381210432017362901850553 1035907824013022176387915)
          ·
            refine ⟨1553861736019533264581873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035907824013022176387915 1553861736019533264581873)
            ·
              refine ⟨1165396302014649948436405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553861736019533264581873 1165396302014649948436405)
              ·
                refine ⟨109255903313873432665913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1165396302014649948436405 109255903313873432665913)
                ·
                  rfl

theorem cell19_359058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_359058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359058 prefixEnd_359058 := by exact prefixLift 359058
  have htrace : WordTrace (prefixWord ++ tailWord_359058) baseStart_359058 baseEnd_359058 := by
    simpa [prefixWord, tailWord_359058, baseEnd_359058] using wordTrace_append hprefix tailTrace_359058
  have hstable : (prefixWord ++ tailWord_359058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359058).length < 2 ^ (prefixWord ++ tailWord_359058).sum := by decide
  have hdescent : baseEnd_359058 < baseStart_359058 := by decide
  rcases family_descends (prefixWord ++ tailWord_359058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359170 : List Nat := [3, 4, 1, 1, 1, 2, 4, 3]
def baseStart_359170 : Nat := 118140960795 + 359170 * 2 ^ 59
def prefixEnd_359170 : Nat := 4983230072969 + 3 ^ 40 * 359170 * 2
def baseEnd_359170 : Nat := 109289983215090358176719

theorem tailTrace_359170 : CollatzResearch.WordTrace tailWord_359170 prefixEnd_359170 109289983215090358176719 := by
  unfold tailWord_359170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3275001527198976549368741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8733337405863937464983309 3275001527198976549368741)
  ·
    refine ⟨614062786349808103006639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3275001527198976549368741 614062786349808103006639)
    ·
      refine ⟨921094179524712154509959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614062786349808103006639 921094179524712154509959)
      ·
        refine ⟨1381641269287068231764939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921094179524712154509959 1381641269287068231764939)
        ·
          refine ⟨2072461903930602347647409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381641269287068231764939 2072461903930602347647409)
          ·
            refine ⟨1554346427947951760735557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2072461903930602347647409 1554346427947951760735557)
            ·
              refine ⟨291439955240240955137917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1554346427947951760735557 291439955240240955137917)
              ·
                refine ⟨109289983215090358176719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291439955240240955137917 109289983215090358176719)
                ·
                  rfl

theorem cell19_359170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_359170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359170 prefixEnd_359170 := by exact prefixLift 359170
  have htrace : WordTrace (prefixWord ++ tailWord_359170) baseStart_359170 baseEnd_359170 := by
    simpa [prefixWord, tailWord_359170, baseEnd_359170] using wordTrace_append hprefix tailTrace_359170
  have hstable : (prefixWord ++ tailWord_359170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359170).length < 2 ^ (prefixWord ++ tailWord_359170).sum := by decide
  have hdescent : baseEnd_359170 < baseStart_359170 := by decide
  rcases family_descends (prefixWord ++ tailWord_359170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359191 : List Nat := [1, 1, 3, 4, 3, 2, 5]
def baseStart_359191 : Nat := 118140960795 + 359191 * 2 ^ 59
def prefixEnd_359191 : Nat := 4983230072969 + 3 ^ 40 * 359191 * 2
def baseEnd_359191 : Nat := 36432124398856177236665

theorem tailTrace_359191 : CollatzResearch.WordTrace tailWord_359191 prefixEnd_359191 36432124398856177236665 := by
  unfold tailWord_359191
  simp only [CollatzResearch.WordTrace]
  refine ⟨13100772041719826783989427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8733848027813217855992951 13100772041719826783989427)
  ·
    refine ⟨19651158062579740175984141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13100772041719826783989427 19651158062579740175984141)
    ·
      refine ⟨7369184273467402565994053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19651158062579740175984141 7369184273467402565994053)
      ·
        refine ⟨1381722051275137981123885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7369184273467402565994053 1381722051275137981123885)
        ·
          refine ⟨518145769228176742921457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1381722051275137981123885 518145769228176742921457)
          ·
            refine ⟨388609326921132557191093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518145769228176742921457 388609326921132557191093)
            ·
              refine ⟨36432124398856177236665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 388609326921132557191093 36432124398856177236665)
              ·
                rfl

theorem cell19_359191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_359191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359191 prefixEnd_359191 := by exact prefixLift 359191
  have htrace : WordTrace (prefixWord ++ tailWord_359191) baseStart_359191 baseEnd_359191 := by
    simpa [prefixWord, tailWord_359191, baseEnd_359191] using wordTrace_append hprefix tailTrace_359191
  have hstable : (prefixWord ++ tailWord_359191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359191).length < 2 ^ (prefixWord ++ tailWord_359191).sum := by decide
  have hdescent : baseEnd_359191 < baseStart_359191 := by decide
  rcases family_descends (prefixWord ++ tailWord_359191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359212 : List Nat := [2, 2, 1, 1, 1, 4, 4, 4]
def baseStart_359212 : Nat := 118140960795 + 359212 * 2 ^ 59
def prefixEnd_359212 : Nat := 4983230072969 + 3 ^ 40 * 359212 * 2
def baseEnd_359212 : Nat := 109302763178046705243271

theorem tailTrace_359212 : CollatzResearch.WordTrace tailWord_359212 prefixEnd_359212 109302763178046705243271 := by
  unfold tailWord_359212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550768987321873685251945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8734358649762498247002593 6550768987321873685251945)
  ·
    refine ⟨4913076740491405263938959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6550768987321873685251945 4913076740491405263938959)
    ·
      refine ⟨7369615110737107895908439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4913076740491405263938959 7369615110737107895908439)
      ·
        refine ⟨11054422666105661843862659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7369615110737107895908439 11054422666105661843862659)
        ·
          refine ⟨16581633999158492765793989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11054422666105661843862659 16581633999158492765793989)
          ·
            refine ⟨3109056374842217393586373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16581633999158492765793989 3109056374842217393586373)
            ·
              refine ⟨582948070282915761297445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3109056374842217393586373 582948070282915761297445)
              ·
                refine ⟨109302763178046705243271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 582948070282915761297445 109302763178046705243271)
                ·
                  rfl

theorem cell19_359212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_359212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359212 prefixEnd_359212 := by exact prefixLift 359212
  have htrace : WordTrace (prefixWord ++ tailWord_359212) baseStart_359212 baseEnd_359212 := by
    simpa [prefixWord, tailWord_359212, baseEnd_359212] using wordTrace_append hprefix tailTrace_359212
  have hstable : (prefixWord ++ tailWord_359212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359212).length < 2 ^ (prefixWord ++ tailWord_359212).sum := by decide
  have hdescent : baseEnd_359212 < baseStart_359212 := by decide
  rcases family_descends (prefixWord ++ tailWord_359212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359231 : List Nat := [1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_359231 : Nat := 118140960795 + 359231 * 2 ^ 59
def prefixEnd_359231 : Nat := 4983230072969 + 3 ^ 40 * 359231 * 2
def baseEnd_359231 : Nat := 109308544589860290820997

theorem tailTrace_359231 : CollatzResearch.WordTrace tailWord_359231 prefixEnd_359231 109308544589860290820997 := by
  unfold tailWord_359231
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102230961574913615445547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8734820641049942410297031 13102230961574913615445547)
  ·
    refine ⟨19653346442362370423168321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13102230961574913615445547 19653346442362370423168321)
    ·
      refine ⟨14740009831771777817376241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19653346442362370423168321 14740009831771777817376241)
      ·
        refine ⟨11055007373828833363032181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14740009831771777817376241 11055007373828833363032181)
        ·
          refine ⟨1036406941296453127784267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11055007373828833363032181 1036406941296453127784267)
          ·
            refine ⟨1554610411944679691676401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036406941296453127784267 1554610411944679691676401)
            ·
              refine ⟨1165957808958509768757301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1554610411944679691676401 1165957808958509768757301)
              ·
                refine ⟨109308544589860290820997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1165957808958509768757301 109308544589860290820997)
                ·
                  rfl

theorem cell19_359231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_359231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359231 prefixEnd_359231 := by exact prefixLift 359231
  have htrace : WordTrace (prefixWord ++ tailWord_359231) baseStart_359231 baseEnd_359231 := by
    simpa [prefixWord, tailWord_359231, baseEnd_359231] using wordTrace_append hprefix tailTrace_359231
  have hstable : (prefixWord ++ tailWord_359231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359231).length < 2 ^ (prefixWord ++ tailWord_359231).sum := by decide
  have hdescent : baseEnd_359231 < baseStart_359231 := by decide
  rcases family_descends (prefixWord ++ tailWord_359231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359267 : List Nat := [1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_359267 : Nat := 118140960795 + 359267 * 2 ^ 59
def prefixEnd_359267 : Nat := 4983230072969 + 3 ^ 40 * 359267 * 2
def baseEnd_359267 : Nat := 109319498843822874020899

theorem tailTrace_359267 : CollatzResearch.WordTrace tailWord_359267 prefixEnd_359267 109319498843822874020899 := by
  unfold tailWord_359267
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103543989444491763756055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8735695992962994509170703 13103543989444491763756055)
  ·
    refine ⟨19655315984166737645634083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13103543989444491763756055 19655315984166737645634083)
    ·
      refine ⟨29482973976250106468451125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19655315984166737645634083 29482973976250106468451125)
      ·
        refine ⟨2764028810273447481417293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29482973976250106468451125 2764028810273447481417293)
        ·
          refine ⟨1036510803852542805531485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2764028810273447481417293 1036510803852542805531485)
          ·
            refine ⟨388691551444703552074307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1036510803852542805531485 388691551444703552074307)
            ·
              refine ⟨583037327167055328111461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388691551444703552074307 583037327167055328111461)
              ·
                refine ⟨109319498843822874020899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583037327167055328111461 109319498843822874020899)
                ·
                  rfl

theorem cell19_359267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_359267 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359267 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359267 prefixEnd_359267 := by exact prefixLift 359267
  have htrace : WordTrace (prefixWord ++ tailWord_359267) baseStart_359267 baseEnd_359267 := by
    simpa [prefixWord, tailWord_359267, baseEnd_359267] using wordTrace_append hprefix tailTrace_359267
  have hstable : (prefixWord ++ tailWord_359267).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359267).length < 2 ^ (prefixWord ++ tailWord_359267).sum := by decide
  have hdescent : baseEnd_359267 < baseStart_359267 := by decide
  rcases family_descends (prefixWord ++ tailWord_359267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359269 : List Nat := [1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_359269 : Nat := 118140960795 + 359269 * 2 ^ 59
def prefixEnd_359269 : Nat := 4983230072969 + 3 ^ 40 * 359269 * 2
def baseEnd_359269 : Nat := 109320107413487461976449

theorem tailTrace_359269 : CollatzResearch.WordTrace tailWord_359269 prefixEnd_359269 109320107413487461976449 := by
  unfold tailWord_359269
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103616935437246105328861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8735744623624830736885907 13103616935437246105328861)
  ·
    refine ⟨4913856350788967289498323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13103616935437246105328861 4913856350788967289498323)
    ·
      refine ⟨7370784526183450934247485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4913856350788967289498323 7370784526183450934247485)
      ·
        refine ⟨2764044197318794100342807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7370784526183450934247485 2764044197318794100342807)
        ·
          refine ⟨4146066295978191150514211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2764044197318794100342807 4146066295978191150514211)
          ·
            refine ⟨6219099443967286725771317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146066295978191150514211 6219099443967286725771317)
            ·
              refine ⟨583040572871933130541061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6219099443967286725771317 583040572871933130541061)
              ·
                refine ⟨109320107413487461976449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583040572871933130541061 109320107413487461976449)
                ·
                  rfl

theorem cell19_359269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_359269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359269 prefixEnd_359269 := by exact prefixLift 359269
  have htrace : WordTrace (prefixWord ++ tailWord_359269) baseStart_359269 baseEnd_359269 := by
    simpa [prefixWord, tailWord_359269, baseEnd_359269] using wordTrace_append hprefix tailTrace_359269
  have hstable : (prefixWord ++ tailWord_359269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359269).length < 2 ^ (prefixWord ++ tailWord_359269).sum := by decide
  have hdescent : baseEnd_359269 < baseStart_359269 := by decide
  rcases family_descends (prefixWord ++ tailWord_359269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359341 : List Nat := [1, 5, 2, 3, 1, 1, 1, 5]
def baseStart_359341 : Nat := 118140960795 + 359341 * 2 ^ 59
def prefixEnd_359341 : Nat := 4983230072969 + 3 ^ 40 * 359341 * 2
def baseEnd_359341 : Nat := 109342015921412628376253

theorem tailTrace_359341 : CollatzResearch.WordTrace tailWord_359341 prefixEnd_359341 109342015921412628376253 := by
  unfold tailWord_359341
  simp only [CollatzResearch.WordTrace]
  refine ⟨13106242991176402401949877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8737495327450934934633251 13106242991176402401949877)
  ·
    refine ⟨1228710280422787725182801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13106242991176402401949877 1228710280422787725182801)
    ·
      refine ⟨921532710317090793887101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1228710280422787725182801 921532710317090793887101)
      ·
        refine ⟨345574766368909047707663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 921532710317090793887101 345574766368909047707663)
        ·
          refine ⟨518362149553363571561495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345574766368909047707663 518362149553363571561495)
          ·
            refine ⟨777543224330045357342243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518362149553363571561495 777543224330045357342243)
            ·
              refine ⟨1166314836495068036013365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777543224330045357342243 1166314836495068036013365)
              ·
                refine ⟨109342015921412628376253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1166314836495068036013365 109342015921412628376253)
                ·
                  rfl

theorem cell19_359341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_359341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359341 prefixEnd_359341 := by exact prefixLift 359341
  have htrace : WordTrace (prefixWord ++ tailWord_359341) baseStart_359341 baseEnd_359341 := by
    simpa [prefixWord, tailWord_359341, baseEnd_359341] using wordTrace_append hprefix tailTrace_359341
  have hstable : (prefixWord ++ tailWord_359341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359341).length < 2 ^ (prefixWord ++ tailWord_359341).sum := by decide
  have hdescent : baseEnd_359341 < baseStart_359341 := by decide
  rcases family_descends (prefixWord ++ tailWord_359341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359381 : List Nat := [1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_359381 : Nat := 118140960795 + 359381 * 2 ^ 59
def prefixEnd_359381 : Nat := 4983230072969 + 3 ^ 40 * 359381 * 2
def baseEnd_359381 : Nat := 109354187314704387487255

theorem tailTrace_359381 : CollatzResearch.WordTrace tailWord_359381 prefixEnd_359381 109354187314704387487255 := by
  unfold tailWord_359381
  simp only [CollatzResearch.WordTrace]
  refine ⟨13107701911031489233405997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8738467940687659488937331 13107701911031489233405997)
  ·
    refine ⟨4915388216636808462527249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13107701911031489233405997 4915388216636808462527249)
    ·
      refine ⟨3686541162477606346895437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4915388216636808462527249 3686541162477606346895437)
      ·
        refine ⟨1382452935929102380085789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3686541162477606346895437 1382452935929102380085789)
        ·
          refine ⟨518419850973413392532171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1382452935929102380085789 518419850973413392532171)
          ·
            refine ⟨777629776460120088798257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518419850973413392532171 777629776460120088798257)
            ·
              refine ⟨583222332345090066598693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777629776460120088798257 583222332345090066598693)
              ·
                refine ⟨109354187314704387487255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583222332345090066598693 109354187314704387487255)
                ·
                  rfl

theorem cell19_359381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_359381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359381 prefixEnd_359381 := by exact prefixLift 359381
  have htrace : WordTrace (prefixWord ++ tailWord_359381) baseStart_359381 baseEnd_359381 := by
    simpa [prefixWord, tailWord_359381, baseEnd_359381] using wordTrace_append hprefix tailTrace_359381
  have hstable : (prefixWord ++ tailWord_359381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359381).length < 2 ^ (prefixWord ++ tailWord_359381).sum := by decide
  have hdescent : baseEnd_359381 < baseStart_359381 := by decide
  rcases family_descends (prefixWord ++ tailWord_359381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359402 : List Nat := [3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_359402 : Nat := 118140960795 + 359402 * 2 ^ 59
def prefixEnd_359402 : Nat := 4983230072969 + 3 ^ 40 * 359402 * 2
def baseEnd_359402 : Nat := 109360577296182561020531

theorem tailTrace_359402 : CollatzResearch.WordTrace tailWord_359402 prefixEnd_359402 109360577296182561020531 := by
  unfold tailWord_359402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277116960988852454980115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8738978562636939879946973 3277116960988852454980115)
  ·
    refine ⟨4915675441483278682470173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3277116960988852454980115 4915675441483278682470173)
    ·
      refine ⟨1843378290556229505926315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4915675441483278682470173 1843378290556229505926315)
      ·
        refine ⟨2765067435834344258889473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843378290556229505926315 2765067435834344258889473)
        ·
          refine ⟨2073800576875758194167105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765067435834344258889473 2073800576875758194167105)
          ·
            refine ⟨1555350432656818645625329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2073800576875758194167105 1555350432656818645625329)
            ·
              refine ⟨1166512824492613984218997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1555350432656818645625329 1166512824492613984218997)
              ·
                refine ⟨109360577296182561020531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1166512824492613984218997 109360577296182561020531)
                ·
                  rfl

theorem cell19_359402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_359402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359402 prefixEnd_359402 := by exact prefixLift 359402
  have htrace : WordTrace (prefixWord ++ tailWord_359402) baseStart_359402 baseEnd_359402 := by
    simpa [prefixWord, tailWord_359402, baseEnd_359402] using wordTrace_append hprefix tailTrace_359402
  have hstable : (prefixWord ++ tailWord_359402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359402).length < 2 ^ (prefixWord ++ tailWord_359402).sum := by decide
  have hdescent : baseEnd_359402 < baseStart_359402 := by decide
  rcases family_descends (prefixWord ++ tailWord_359402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359438 : List Nat := [4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_359438 : Nat := 118140960795 + 359438 * 2 ^ 59
def prefixEnd_359438 : Nat := 4983230072969 + 3 ^ 40 * 359438 * 2
def baseEnd_359438 : Nat := 109371531550145144220433

theorem tailTrace_359438 : CollatzResearch.WordTrace tailWord_359438 prefixEnd_359438 109371531550145144220433 := by
  unfold tailWord_359438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1638722608978123496028871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8739853914549991978820645 1638722608978123496028871)
  ·
    refine ⟨2458083913467185244043307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1638722608978123496028871 2458083913467185244043307)
    ·
      refine ⟨3687125870200777866064961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2458083913467185244043307 3687125870200777866064961)
      ·
        refine ⟨2765344402650583399548721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3687125870200777866064961 2765344402650583399548721)
        ·
          refine ⟨2074008301987937549661541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765344402650583399548721 2074008301987937549661541)
          ·
            refine ⟨388876556622738290561539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2074008301987937549661541 388876556622738290561539)
            ·
              refine ⟨583314834934107435842309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388876556622738290561539 583314834934107435842309)
              ·
                refine ⟨109371531550145144220433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583314834934107435842309 109371531550145144220433)
                ·
                  rfl

theorem cell19_359438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_359438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359438 prefixEnd_359438 := by exact prefixLift 359438
  have htrace : WordTrace (prefixWord ++ tailWord_359438) baseStart_359438 baseEnd_359438 := by
    simpa [prefixWord, tailWord_359438, baseEnd_359438] using wordTrace_append hprefix tailTrace_359438
  have hstable : (prefixWord ++ tailWord_359438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359438).length < 2 ^ (prefixWord ++ tailWord_359438).sum := by decide
  have hdescent : baseEnd_359438 < baseStart_359438 := by decide
  rcases family_descends (prefixWord ++ tailWord_359438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359457 : List Nat := [1, 2, 3, 2, 3, 2, 3, 3]
def baseStart_359457 : Nat := 118140960795 + 359457 * 2 ^ 59
def prefixEnd_359457 : Nat := 4983230072969 + 3 ^ 40 * 359457 * 2
def baseEnd_359457 : Nat := 109377312961958729798159

theorem tailTrace_359457 : CollatzResearch.WordTrace tailWord_359457 prefixEnd_359457 109377312961958729798159 := by
  unfold tailWord_359457
  simp only [CollatzResearch.WordTrace]
  refine ⟨13110473858756154213172625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8740315905837436142115083 13110473858756154213172625)
  ·
    refine ⟨9832855394067115659879469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13110473858756154213172625 9832855394067115659879469)
    ·
      refine ⟨3687320772775168372454801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9832855394067115659879469 3687320772775168372454801)
      ·
        refine ⟨2765490579581376279341101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3687320772775168372454801 2765490579581376279341101)
        ·
          refine ⟨1037058967343016104752913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2765490579581376279341101 1037058967343016104752913)
          ·
            refine ⟨777794225507262078564685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037058967343016104752913 777794225507262078564685)
            ·
              refine ⟨291672834565223279461757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 777794225507262078564685 291672834565223279461757)
              ·
                refine ⟨109377312961958729798159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291672834565223279461757 109377312961958729798159)
                ·
                  rfl

theorem cell19_359457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_359457 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359457 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359457 prefixEnd_359457 := by exact prefixLift 359457
  have htrace : WordTrace (prefixWord ++ tailWord_359457) baseStart_359457 baseEnd_359457 := by
    simpa [prefixWord, tailWord_359457, baseEnd_359457] using wordTrace_append hprefix tailTrace_359457
  have hstable : (prefixWord ++ tailWord_359457).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359457).length < 2 ^ (prefixWord ++ tailWord_359457).sum := by decide
  have hdescent : baseEnd_359457 < baseStart_359457 := by decide
  rcases family_descends (prefixWord ++ tailWord_359457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359476 : List Nat := [2, 5, 1, 2, 1, 2, 6]
def baseStart_359476 : Nat := 118140960795 + 359476 * 2 ^ 59
def prefixEnd_359476 : Nat := 4983230072969 + 3 ^ 40 * 359476 * 2
def baseEnd_359476 : Nat := 36461031457924105125295

theorem tailTrace_359476 : CollatzResearch.WordTrace tailWord_359476 prefixEnd_359476 36461031457924105125295 := by
  unfold tailWord_359476
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555583422843660229057141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8740777897124880305409521 6555583422843660229057141)
  ·
    refine ⟨614585945891593146474107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6555583422843660229057141 614585945891593146474107)
    ·
      refine ⟨921878918837389719711161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 614585945891593146474107 921878918837389719711161)
      ·
        refine ⟨691409189128042289783371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 921878918837389719711161 691409189128042289783371)
        ·
          refine ⟨1037113783692063434675057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691409189128042289783371 1037113783692063434675057)
          ·
            refine ⟨777835337769047576006293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037113783692063434675057 777835337769047576006293)
            ·
              refine ⟨36461031457924105125295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 777835337769047576006293 36461031457924105125295)
              ·
                rfl

theorem cell19_359476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_359476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359476 prefixEnd_359476 := by exact prefixLift 359476
  have htrace : WordTrace (prefixWord ++ tailWord_359476) baseStart_359476 baseEnd_359476 := by
    simpa [prefixWord, tailWord_359476, baseEnd_359476] using wordTrace_append hprefix tailTrace_359476
  have hstable : (prefixWord ++ tailWord_359476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359476).length < 2 ^ (prefixWord ++ tailWord_359476).sum := by decide
  have hdescent : baseEnd_359476 < baseStart_359476 := by decide
  rcases family_descends (prefixWord ++ tailWord_359476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359516 : List Nat := [2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_359516 : Nat := 118140960795 + 359516 * 2 ^ 59
def prefixEnd_359516 : Nat := 4983230072969 + 3 ^ 40 * 359516 * 2
def baseEnd_359516 : Nat := 109395265767064074486887

theorem tailTrace_359516 : CollatzResearch.WordTrace tailWord_359516 prefixEnd_359516 109395265767064074486887 := by
  unfold tailWord_359516
  simp only [CollatzResearch.WordTrace]
  refine ⟨6556312882771203644785201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8741750510361604859713601 6556312882771203644785201)
  ·
    refine ⟨4917234662078402733588901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6556312882771203644785201 4917234662078402733588901)
    ·
      refine ⟨921981499139700512547919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4917234662078402733588901 921981499139700512547919)
      ·
        refine ⟨1382972248709550768821879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921981499139700512547919 1382972248709550768821879)
        ·
          refine ⟨2074458373064326153232819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1382972248709550768821879 2074458373064326153232819)
          ·
            refine ⟨3111687559596489229849229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074458373064326153232819 3111687559596489229849229)
            ·
              refine ⟨1166882834848683461193461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3111687559596489229849229 1166882834848683461193461)
              ·
                refine ⟨109395265767064074486887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1166882834848683461193461 109395265767064074486887)
                ·
                  rfl

theorem cell19_359516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_359516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359516 prefixEnd_359516 := by exact prefixLift 359516
  have htrace : WordTrace (prefixWord ++ tailWord_359516) baseStart_359516 baseEnd_359516 := by
    simpa [prefixWord, tailWord_359516, baseEnd_359516] using wordTrace_append hprefix tailTrace_359516
  have hstable : (prefixWord ++ tailWord_359516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359516).length < 2 ^ (prefixWord ++ tailWord_359516).sum := by decide
  have hdescent : baseEnd_359516 < baseStart_359516 := by decide
  rcases family_descends (prefixWord ++ tailWord_359516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359622 : List Nat := [6, 1, 2, 2, 1, 1, 3, 3]
def baseStart_359622 : Nat := 118140960795 + 359622 * 2 ^ 59
def prefixEnd_359622 : Nat := 4983230072969 + 3 ^ 40 * 359622 * 2
def baseEnd_359622 : Nat := 109427519959287236131043

theorem tailTrace_359622 : CollatzResearch.WordTrace tailWord_359622 prefixEnd_359622 109427519959287236131043 := by
  unfold tailWord_359622
  simp only [CollatzResearch.WordTrace]
  refine ⟨409890371973699606029035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8744327935438924928619413 409890371973699606029035)
  ·
    refine ⟨614835557960549409043553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409890371973699606029035 614835557960549409043553)
    ·
      refine ⟨461126668470412056782665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 614835557960549409043553 461126668470412056782665)
      ·
        refine ⟨345845001352809042586999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461126668470412056782665 345845001352809042586999)
        ·
          refine ⟨518767502029213563880499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345845001352809042586999 518767502029213563880499)
          ·
            refine ⟨778151253043820345820749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518767502029213563880499 778151253043820345820749)
            ·
              refine ⟨291806719891432629682781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 778151253043820345820749 291806719891432629682781)
              ·
                refine ⟨109427519959287236131043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291806719891432629682781 109427519959287236131043)
                ·
                  rfl

theorem cell19_359622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_359622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359622 prefixEnd_359622 := by exact prefixLift 359622
  have htrace : WordTrace (prefixWord ++ tailWord_359622) baseStart_359622 baseEnd_359622 := by
    simpa [prefixWord, tailWord_359622, baseEnd_359622] using wordTrace_append hprefix tailTrace_359622
  have hstable : (prefixWord ++ tailWord_359622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359622).length < 2 ^ (prefixWord ++ tailWord_359622).sum := by decide
  have hdescent : baseEnd_359622 < baseStart_359622 := by decide
  rcases family_descends (prefixWord ++ tailWord_359622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359689 : List Nat := [1, 2, 1, 1, 3, 3, 3, 5]
def baseStart_359689 : Nat := 118140960795 + 359689 * 2 ^ 59
def prefixEnd_359689 : Nat := 4983230072969 + 3 ^ 40 * 359689 * 2
def baseEnd_359689 : Nat := 109447907043050932641971

theorem tailTrace_359689 : CollatzResearch.WordTrace tailWord_359689 prefixEnd_359689 109447907043050932641971 := by
  unfold tailWord_359689
  simp only [CollatzResearch.WordTrace]
  refine ⟨13118935593915657835618121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8745957062610438557078747 13118935593915657835618121)
  ·
    refine ⟨9839201695436743376713591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13118935593915657835618121 9839201695436743376713591)
    ·
      refine ⟨14758802543155115065070387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9839201695436743376713591 14758802543155115065070387)
      ·
        refine ⟨22138203814732672597605581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14758802543155115065070387 22138203814732672597605581)
        ·
          refine ⟨8301826430524752224102093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22138203814732672597605581 8301826430524752224102093)
          ·
            refine ⟨3113184911446782084038285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8301826430524752224102093 3113184911446782084038285)
            ·
              refine ⟨1167444341792543281514357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3113184911446782084038285 1167444341792543281514357)
              ·
                refine ⟨109447907043050932641971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1167444341792543281514357 109447907043050932641971)
                ·
                  rfl

theorem cell19_359689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_359689 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359689 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359689 prefixEnd_359689 := by exact prefixLift 359689
  have htrace : WordTrace (prefixWord ++ tailWord_359689) baseStart_359689 baseEnd_359689 := by
    simpa [prefixWord, tailWord_359689, baseEnd_359689] using wordTrace_append hprefix tailTrace_359689
  have hstable : (prefixWord ++ tailWord_359689).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359689).length < 2 ^ (prefixWord ++ tailWord_359689).sum := by decide
  have hdescent : baseEnd_359689 < baseStart_359689 := by decide
  rcases family_descends (prefixWord ++ tailWord_359689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359706 : List Nat := [3, 1, 1, 3, 3, 3, 5]
def baseStart_359706 : Nat := 118140960795 + 359706 * 2 ^ 59
def prefixEnd_359706 : Nat := 4983230072969 + 3 ^ 40 * 359706 * 2
def baseEnd_359706 : Nat := 36484359961733310088049

theorem tailTrace_359706 : CollatzResearch.WordTrace tailWord_359706 prefixEnd_359706 36484359961733310088049 := by
  unfold tailWord_359706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279888908713517434746743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8746370423236046492657981 3279888908713517434746743)
  ·
    refine ⟨4919833363070276152120115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3279888908713517434746743 4919833363070276152120115)
    ·
      refine ⟨7379750044605414228180173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919833363070276152120115 7379750044605414228180173)
      ·
        refine ⟨2767406266727030335567565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7379750044605414228180173 2767406266727030335567565)
        ·
          refine ⟨1037777350022636375837837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2767406266727030335567565 1037777350022636375837837)
          ·
            refine ⟨389166506258488640939189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1037777350022636375837837 389166506258488640939189)
            ·
              refine ⟨36484359961733310088049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 389166506258488640939189 36484359961733310088049)
              ·
                rfl

theorem cell19_359706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_359706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359706 prefixEnd_359706 := by exact prefixLift 359706
  have htrace : WordTrace (prefixWord ++ tailWord_359706) baseStart_359706 baseEnd_359706 := by
    simpa [prefixWord, tailWord_359706, baseEnd_359706] using wordTrace_append hprefix tailTrace_359706
  have hstable : (prefixWord ++ tailWord_359706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359706).length < 2 ^ (prefixWord ++ tailWord_359706).sum := by decide
  have hdescent : baseEnd_359706 < baseStart_359706 := by decide
  rcases family_descends (prefixWord ++ tailWord_359706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359708 : List Nat := [2, 2, 3, 1, 1, 1, 9]
def baseStart_359708 : Nat := 118140960795 + 359708 * 2 ^ 59
def prefixEnd_359708 : Nat := 4983230072969 + 3 ^ 40 * 359708 * 2
def baseEnd_359708 : Nat := 36484562818288172739899

theorem tailTrace_359708 : CollatzResearch.WordTrace tailWord_359708 prefixEnd_359708 36484562818288172739899 := by
  unfold tailWord_359708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559814290423412040279889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8746419053897882720373185 6559814290423412040279889)
  ·
    refine ⟨4919860717817559030209917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6559814290423412040279889 4919860717817559030209917)
    ·
      refine ⟨1844947769181584636328719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4919860717817559030209917 1844947769181584636328719)
      ·
        refine ⟨2767421653772376954493079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844947769181584636328719 2767421653772376954493079)
        ·
          refine ⟨4151132480658565431739619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767421653772376954493079 4151132480658565431739619)
          ·
            refine ⟨6226698720987848147609429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4151132480658565431739619 6226698720987848147609429)
            ·
              refine ⟨36484562818288172739899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6226698720987848147609429 36484562818288172739899)
              ·
                rfl

theorem cell19_359708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_359708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359708 prefixEnd_359708 := by exact prefixLift 359708
  have htrace : WordTrace (prefixWord ++ tailWord_359708) baseStart_359708 baseEnd_359708 := by
    simpa [prefixWord, tailWord_359708, baseEnd_359708] using wordTrace_append hprefix tailTrace_359708
  have hstable : (prefixWord ++ tailWord_359708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359708).length < 2 ^ (prefixWord ++ tailWord_359708).sum := by decide
  have hdescent : baseEnd_359708 < baseStart_359708 := by decide
  rcases family_descends (prefixWord ++ tailWord_359708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359765 : List Nat := [1, 3, 2, 2, 3, 8]
def baseStart_359765 : Nat := 118140960795 + 359765 * 2 ^ 59
def prefixEnd_359765 : Nat := 4983230072969 + 3 ^ 40 * 359765 * 2
def baseEnd_359765 : Nat := 12163448076700586105875

theorem tailTrace_359765 : CollatzResearch.WordTrace tailWord_359765 prefixEnd_359765 12163448076700586105875 := by
  unfold tailWord_359765
  simp only [CollatzResearch.WordTrace]
  refine ⟨13121707541640322815384749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8747805027760215210256499 13121707541640322815384749)
  ·
    refine ⟨4920640328115121055769281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13121707541640322815384749 4920640328115121055769281)
    ·
      refine ⟨3690480246086340791826961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4920640328115121055769281 3690480246086340791826961)
      ·
        refine ⟨2767860184564755593870221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3690480246086340791826961 2767860184564755593870221)
        ·
          refine ⟨1037947569211783347701333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2767860184564755593870221 1037947569211783347701333)
          ·
            refine ⟨12163448076700586105875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1037947569211783347701333 12163448076700586105875)
            ·
              rfl

theorem cell19_359765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 8].length) (baseStart_359765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359765 prefixEnd_359765 := by exact prefixLift 359765
  have htrace : WordTrace (prefixWord ++ tailWord_359765) baseStart_359765 baseEnd_359765 := by
    simpa [prefixWord, tailWord_359765, baseEnd_359765] using wordTrace_append hprefix tailTrace_359765
  have hstable : (prefixWord ++ tailWord_359765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359765).length < 2 ^ (prefixWord ++ tailWord_359765).sum := by decide
  have hdescent : baseEnd_359765 < baseStart_359765 := by decide
  rcases family_descends (prefixWord ++ tailWord_359765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359894 : List Nat := [5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_359894 : Nat := 118140960795 + 359894 * 2 ^ 59
def prefixEnd_359894 : Nat := 4983230072969 + 3 ^ 40 * 359894 * 2
def baseEnd_359894 : Nat := 109510285433671198085857

theorem tailTrace_359894 : CollatzResearch.WordTrace tailWord_359894 prefixEnd_359894 109510285433671198085857 := by
  unfold tailWord_359894
  simp only [CollatzResearch.WordTrace]
  refine ⟨820400784885811115426921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8750941705448651897887157 820400784885811115426921)
  ·
    refine ⟨615300588664358336570191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 820400784885811115426921 615300588664358336570191)
    ·
      refine ⟨922950882996537504855287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615300588664358336570191 922950882996537504855287)
      ·
        refine ⟨1384426324494806257282931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922950882996537504855287 1384426324494806257282931)
        ·
          refine ⟨2076639486742209385924397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384426324494806257282931 2076639486742209385924397)
          ·
            refine ⟨778739807528328519721649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2076639486742209385924397 778739807528328519721649)
            ·
              refine ⟨584054855646246389791237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778739807528328519721649 584054855646246389791237)
              ·
                refine ⟨109510285433671198085857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 584054855646246389791237 109510285433671198085857)
                ·
                  rfl

theorem cell19_359894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_359894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359894 prefixEnd_359894 := by exact prefixLift 359894
  have htrace : WordTrace (prefixWord ++ tailWord_359894) baseStart_359894 baseEnd_359894 := by
    simpa [prefixWord, tailWord_359894, baseEnd_359894] using wordTrace_append hprefix tailTrace_359894
  have hstable : (prefixWord ++ tailWord_359894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359894).length < 2 ^ (prefixWord ++ tailWord_359894).sum := by decide
  have hdescent : baseEnd_359894 < baseStart_359894 := by decide
  rcases family_descends (prefixWord ++ tailWord_359894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359898 : List Nat := [3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_359898 : Nat := 118140960795 + 359898 * 2 ^ 59
def prefixEnd_359898 : Nat := 4983230072969 + 3 ^ 40 * 359898 * 2
def baseEnd_359898 : Nat := 109511502573000373996957

theorem tailTrace_359898 : CollatzResearch.WordTrace tailWord_359898 prefixEnd_359898 109511502573000373996957 := by
  unfold tailWord_359898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281639612539621632494087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8751038966772324353317565 3281639612539621632494087)
  ·
    refine ⟨4922459418809432448741131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3281639612539621632494087 4922459418809432448741131)
    ·
      refine ⟨7383689128214148673111697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4922459418809432448741131 7383689128214148673111697)
      ·
        refine ⟨5537766846160611504833773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7383689128214148673111697 5537766846160611504833773)
        ·
          refine ⟨2076662567310229314312665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5537766846160611504833773 2076662567310229314312665)
          ·
            refine ⟨1557496925482671985734499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2076662567310229314312665 1557496925482671985734499)
            ·
              refine ⟨2336245388224007978601749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557496925482671985734499 2336245388224007978601749)
              ·
                refine ⟨109511502573000373996957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2336245388224007978601749 109511502573000373996957)
                ·
                  rfl

theorem cell19_359898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_359898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359898 prefixEnd_359898 := by exact prefixLift 359898
  have htrace : WordTrace (prefixWord ++ tailWord_359898) baseStart_359898 baseEnd_359898 := by
    simpa [prefixWord, tailWord_359898, baseEnd_359898] using wordTrace_append hprefix tailTrace_359898
  have hstable : (prefixWord ++ tailWord_359898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359898).length < 2 ^ (prefixWord ++ tailWord_359898).sum := by decide
  have hdescent : baseEnd_359898 < baseStart_359898 := by decide
  rcases family_descends (prefixWord ++ tailWord_359898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359934 : List Nat := [4, 2, 2, 3, 8]
def baseStart_359934 : Nat := 118140960795 + 359934 * 2 ^ 59
def prefixEnd_359934 : Nat := 4983230072969 + 3 ^ 40 * 359934 * 2
def baseEnd_359934 : Nat := 4056387289887516933217

theorem tailTrace_359934 : CollatzResearch.WordTrace tailWord_359934 prefixEnd_359934 4056387289887516933217 := by
  unfold tailWord_359934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640983934753508084785857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8751914318685376452191237 1640983934753508084785857)
  ·
    refine ⟨1230737951065131063589393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1640983934753508084785857 1230737951065131063589393)
    ·
      refine ⟨923053463298848297692045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1230737951065131063589393 923053463298848297692045)
      ·
        refine ⟨346145048737068111634517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 923053463298848297692045 346145048737068111634517)
        ·
          refine ⟨4056387289887516933217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 346145048737068111634517 4056387289887516933217)
          ·
            rfl

theorem cell19_359934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 8].length) (baseStart_359934 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359934 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359934 prefixEnd_359934 := by exact prefixLift 359934
  have htrace : WordTrace (prefixWord ++ tailWord_359934) baseStart_359934 baseEnd_359934 := by
    simpa [prefixWord, tailWord_359934, baseEnd_359934] using wordTrace_append hprefix tailTrace_359934
  have hstable : (prefixWord ++ tailWord_359934).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359934).length < 2 ^ (prefixWord ++ tailWord_359934).sum := by decide
  have hdescent : baseEnd_359934 < baseStart_359934 := by decide
  rcases family_descends (prefixWord ++ tailWord_359934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359955 : List Nat := [1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_359955 : Nat := 118140960795 + 359955 * 2 ^ 59
def prefixEnd_359955 : Nat := 4983230072969 + 3 ^ 40 * 359955 * 2
def baseEnd_359955 : Nat := 109528846808441130730135

theorem tailTrace_359955 : CollatzResearch.WordTrace tailWord_359955 prefixEnd_359955 109528846808441130730135 := by
  unfold tailWord_359955
  simp only [CollatzResearch.WordTrace]
  refine ⟨13128637410951985264801319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8752424940634656843200879 13128637410951985264801319)
  ·
    refine ⟨19692956116427977897201979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13128637410951985264801319 19692956116427977897201979)
    ·
      refine ⟨29539434174641966845802969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19692956116427977897201979 29539434174641966845802969)
      ·
        refine ⟨22154575630981475134352227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29539434174641966845802969 22154575630981475134352227)
        ·
          refine ⟨33231863446472212701528341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22154575630981475134352227 33231863446472212701528341)
          ·
            refine ⟨1557743599053384970384141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33231863446472212701528341 1557743599053384970384141)
            ·
              refine ⟨584153849645019363894053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1557743599053384970384141 584153849645019363894053)
              ·
                refine ⟨109528846808441130730135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 584153849645019363894053 109528846808441130730135)
                ·
                  rfl

theorem cell19_359955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_359955 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359955 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359955 prefixEnd_359955 := by exact prefixLift 359955
  have htrace : WordTrace (prefixWord ++ tailWord_359955) baseStart_359955 baseEnd_359955 := by
    simpa [prefixWord, tailWord_359955, baseEnd_359955] using wordTrace_append hprefix tailTrace_359955
  have hstable : (prefixWord ++ tailWord_359955).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359955).length < 2 ^ (prefixWord ++ tailWord_359955).sum := by decide
  have hdescent : baseEnd_359955 < baseStart_359955 := by decide
  rcases family_descends (prefixWord ++ tailWord_359955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359993 : List Nat := [1, 2, 1, 5, 1, 3, 6]
def baseStart_359993 : Nat := 118140960795 + 359993 * 2 ^ 59
def prefixEnd_359993 : Nat := 4983230072969 + 3 ^ 40 * 359993 * 2
def baseEnd_359993 : Nat := 36513469877356100628529

theorem tailTrace_359993 : CollatzResearch.WordTrace tailWord_359993 prefixEnd_359993 36513469877356100628529 := by
  unfold tailWord_359993
  simp only [CollatzResearch.WordTrace]
  refine ⟨13130023384814317754684633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8753348923209545169789755 13130023384814317754684633)
  ·
    refine ⟨9847517538610738316013475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13130023384814317754684633 9847517538610738316013475)
    ·
      refine ⟨14771276307916107474020213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9847517538610738316013475 14771276307916107474020213)
      ·
        refine ⟨1384807153867135075689395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14771276307916107474020213 1384807153867135075689395)
        ·
          refine ⟨2077210730800702613534093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384807153867135075689395 2077210730800702613534093)
          ·
            refine ⟨778954024050263480075285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2077210730800702613534093 778954024050263480075285)
            ·
              refine ⟨36513469877356100628529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 778954024050263480075285 36513469877356100628529)
              ·
                rfl

theorem cell19_359993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_359993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_359993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_359993 prefixEnd_359993 := by exact prefixLift 359993
  have htrace : WordTrace (prefixWord ++ tailWord_359993) baseStart_359993 baseEnd_359993 := by
    simpa [prefixWord, tailWord_359993, baseEnd_359993] using wordTrace_append hprefix tailTrace_359993
  have hstable : (prefixWord ++ tailWord_359993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359993).length < 2 ^ (prefixWord ++ tailWord_359993).sum := by decide
  have hdescent : baseEnd_359993 < baseStart_359993 := by decide
  rcases family_descends (prefixWord ++ tailWord_359993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360046 : List Nat := [4, 1, 2, 2, 4, 1, 5]
def baseStart_360046 : Nat := 118140960795 + 360046 * 2 ^ 59
def prefixEnd_360046 : Nat := 4983230072969 + 3 ^ 40 * 360046 * 2
def baseEnd_360046 : Nat := 36518845576059960902555

theorem tailTrace_360046 : CollatzResearch.WordTrace tailWord_360046 prefixEnd_360046 36518845576059960902555 := by
  unfold tailWord_360046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641494556702788475795499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8754637635748205204242661 1641494556702788475795499)
  ·
    refine ⟨2462241835054182713693249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1641494556702788475795499 2462241835054182713693249)
    ·
      refine ⟨1846681376290637035269937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2462241835054182713693249 1846681376290637035269937)
      ·
        refine ⟨1385011032217977776452453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1846681376290637035269937 1385011032217977776452453)
        ·
          refine ⟨259689568540870833084835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1385011032217977776452453 259689568540870833084835)
          ·
            refine ⟨389534352811306249627253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259689568540870833084835 389534352811306249627253)
            ·
              refine ⟨36518845576059960902555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 389534352811306249627253 36518845576059960902555)
              ·
                rfl

theorem cell19_360046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 5].length) (baseStart_360046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360046 prefixEnd_360046 := by exact prefixLift 360046
  have htrace : WordTrace (prefixWord ++ tailWord_360046) baseStart_360046 baseEnd_360046 := by
    simpa [prefixWord, tailWord_360046, baseEnd_360046] using wordTrace_append hprefix tailTrace_360046
  have hstable : (prefixWord ++ tailWord_360046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360046).length < 2 ^ (prefixWord ++ tailWord_360046).sum := by decide
  have hdescent : baseEnd_360046 < baseStart_360046 := by decide
  rcases family_descends (prefixWord ++ tailWord_360046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360050 : List Nat := [3, 2, 1, 2, 3, 1, 7]
def baseStart_360050 : Nat := 118140960795 + 360050 * 2 ^ 59
def prefixEnd_360050 : Nat := 4983230072969 + 3 ^ 40 * 360050 * 2
def baseEnd_360050 : Nat := 36519251289169686206255

theorem tailTrace_360050 : CollatzResearch.WordTrace tailWord_360050 prefixEnd_360050 36519251289169686206255 := by
  unfold tailWord_360050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3283025586401954122377401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8754734897071877659673069 3283025586401954122377401)
  ·
    refine ⟨2462269189801465591783051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3283025586401954122377401 2462269189801465591783051)
    ·
      refine ⟨3693403784702198387674577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2462269189801465591783051 3693403784702198387674577)
      ·
        refine ⟨2770052838526648790755933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3693403784702198387674577 2770052838526648790755933)
        ·
          refine ⟨1038769814447493296533475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2770052838526648790755933 1038769814447493296533475)
          ·
            refine ⟨1558154721671239944800213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038769814447493296533475 1558154721671239944800213)
            ·
              refine ⟨36519251289169686206255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1558154721671239944800213 36519251289169686206255)
              ·
                rfl

theorem cell19_360050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_360050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360050 prefixEnd_360050 := by exact prefixLift 360050
  have htrace : WordTrace (prefixWord ++ tailWord_360050) baseStart_360050 baseEnd_360050 := by
    simpa [prefixWord, tailWord_360050, baseEnd_360050] using wordTrace_append hprefix tailTrace_360050
  have hstable : (prefixWord ++ tailWord_360050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360050).length < 2 ^ (prefixWord ++ tailWord_360050).sum := by decide
  have hdescent : baseEnd_360050 < baseStart_360050 := by decide
  rcases family_descends (prefixWord ++ tailWord_360050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360069 : List Nat := [1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_360069 : Nat := 118140960795 + 360069 * 2 ^ 59
def prefixEnd_360069 : Nat := 4983230072969 + 3 ^ 40 * 360069 * 2
def baseEnd_360069 : Nat := 109563535279322644196491

theorem tailTrace_360069 : CollatzResearch.WordTrace tailWord_360069 prefixEnd_360069 109563535279322644196491 := by
  unfold tailWord_360069
  simp only [CollatzResearch.WordTrace]
  refine ⟨13132795332538982734451261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8755196888359321822967507 13132795332538982734451261)
  ·
    refine ⟨4924798249702118525419223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13132795332538982734451261 4924798249702118525419223)
    ·
      refine ⟨7387197374553177788128835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4924798249702118525419223 7387197374553177788128835)
      ·
        refine ⟨11080796061829766682193253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7387197374553177788128835 11080796061829766682193253)
        ·
          refine ⟨2077649261593081252911235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11080796061829766682193253 2077649261593081252911235)
          ·
            refine ⟨3116473892389621879366853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077649261593081252911235 3116473892389621879366853)
            ·
              refine ⟨584338854823054102381285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3116473892389621879366853 584338854823054102381285)
              ·
                refine ⟨109563535279322644196491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 584338854823054102381285 109563535279322644196491)
                ·
                  rfl

theorem cell19_360069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_360069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360069 prefixEnd_360069 := by exact prefixLift 360069
  have htrace : WordTrace (prefixWord ++ tailWord_360069) baseStart_360069 baseEnd_360069 := by
    simpa [prefixWord, tailWord_360069, baseEnd_360069] using wordTrace_append hprefix tailTrace_360069
  have hstable : (prefixWord ++ tailWord_360069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360069).length < 2 ^ (prefixWord ++ tailWord_360069).sum := by decide
  have hdescent : baseEnd_360069 < baseStart_360069 := by decide
  rcases family_descends (prefixWord ++ tailWord_360069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360088 : List Nat := [2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_360088 : Nat := 118140960795 + 360088 * 2 ^ 59
def prefixEnd_360088 : Nat := 4983230072969 + 3 ^ 40 * 360088 * 2
def baseEnd_360088 : Nat := 109569316691136229774217

theorem tailTrace_360088 : CollatzResearch.WordTrace tailWord_360088 prefixEnd_360088 109569316691136229774217 := by
  unfold tailWord_360088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566744159735074489696459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8755658879646765986261945 6566744159735074489696459)
  ·
    refine ⟨9850116239602611734544689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6566744159735074489696459 9850116239602611734544689)
    ·
      refine ⟨7387587179701958800908517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9850116239602611734544689 7387587179701958800908517)
      ·
        refine ⟨1385172596194117275170347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7387587179701958800908517 1385172596194117275170347)
        ·
          refine ⟨2077758894291175912755521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385172596194117275170347 2077758894291175912755521)
          ·
            refine ⟨1558319170718381934566641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2077758894291175912755521 1558319170718381934566641)
            ·
              refine ⟨1168739378038786450924981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1558319170718381934566641 1168739378038786450924981)
              ·
                refine ⟨109569316691136229774217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1168739378038786450924981 109569316691136229774217)
                ·
                  rfl

theorem cell19_360088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_360088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360088 prefixEnd_360088 := by exact prefixLift 360088
  have htrace : WordTrace (prefixWord ++ tailWord_360088) baseStart_360088 baseEnd_360088 := by
    simpa [prefixWord, tailWord_360088, baseEnd_360088] using wordTrace_append hprefix tailTrace_360088
  have hstable : (prefixWord ++ tailWord_360088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360088).length < 2 ^ (prefixWord ++ tailWord_360088).sum := by decide
  have hdescent : baseEnd_360088 < baseStart_360088 := by decide
  rcases family_descends (prefixWord ++ tailWord_360088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360124 : List Nat := [2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_360124 : Nat := 118140960795 + 360124 * 2 ^ 59
def prefixEnd_360124 : Nat := 4983230072969 + 3 ^ 40 * 360124 * 2
def baseEnd_360124 : Nat := 109580270945098812974119

theorem tailTrace_360124 : CollatzResearch.WordTrace tailWord_360124 prefixEnd_360124 109580270945098812974119 := by
  unfold tailWord_360124
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567400673669863563851713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8756534231559818085135617 6567400673669863563851713)
  ·
    refine ⟨4925550505252397672888785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6567400673669863563851713 4925550505252397672888785)
    ·
      refine ⟨3694162878939298254666589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4925550505252397672888785 3694162878939298254666589)
      ·
        refine ⟨1385311079602236845499971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3694162878939298254666589 1385311079602236845499971)
        ·
          refine ⟨2077966619403355268249957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385311079602236845499971 2077966619403355268249957)
          ·
            refine ⟨389618741138129112796867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2077966619403355268249957 389618741138129112796867)
            ·
              refine ⟨584428111707193669195301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389618741138129112796867 584428111707193669195301)
              ·
                refine ⟨109580270945098812974119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 584428111707193669195301 109580270945098812974119)
                ·
                  rfl

theorem cell19_360124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_360124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360124 prefixEnd_360124 := by exact prefixLift 360124
  have htrace : WordTrace (prefixWord ++ tailWord_360124) baseStart_360124 baseEnd_360124 := by
    simpa [prefixWord, tailWord_360124, baseEnd_360124] using wordTrace_append hprefix tailTrace_360124
  have hstable : (prefixWord ++ tailWord_360124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360124).length < 2 ^ (prefixWord ++ tailWord_360124).sum := by decide
  have hdescent : baseEnd_360124 < baseStart_360124 := by decide
  rcases family_descends (prefixWord ++ tailWord_360124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360202 : List Nat := [3, 1, 2, 2, 1, 4, 1, 5]
def baseStart_360202 : Nat := 118140960795 + 360202 * 2 ^ 59
def prefixEnd_360202 : Nat := 4983230072969 + 3 ^ 40 * 360202 * 2
def baseEnd_360202 : Nat := 109604005162017743240573

theorem tailTrace_360202 : CollatzResearch.WordTrace tailWord_360202 prefixEnd_360202 109604005162017743240573 := by
  unfold tailWord_360202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284411560264286612260715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8758430827371430966028573 3284411560264286612260715)
  ·
    refine ⟨4926617340396429918391073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3284411560264286612260715 4926617340396429918391073)
    ·
      refine ⟨3694963005297322438793305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4926617340396429918391073 3694963005297322438793305)
      ·
        refine ⟨2771222253972991829094979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3694963005297322438793305 2771222253972991829094979)
        ·
          refine ⟨4156833380959487743642469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2771222253972991829094979 4156833380959487743642469)
          ·
            refine ⟨779406258929903951932963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4156833380959487743642469 779406258929903951932963)
            ·
              refine ⟨1169109388394855927899445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779406258929903951932963 1169109388394855927899445)
              ·
                refine ⟨109604005162017743240573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1169109388394855927899445 109604005162017743240573)
                ·
                  rfl

theorem cell19_360202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_360202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360202 prefixEnd_360202 := by exact prefixLift 360202
  have htrace : WordTrace (prefixWord ++ tailWord_360202) baseStart_360202 baseEnd_360202 := by
    simpa [prefixWord, tailWord_360202, baseEnd_360202] using wordTrace_append hprefix tailTrace_360202
  have hstable : (prefixWord ++ tailWord_360202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360202).length < 2 ^ (prefixWord ++ tailWord_360202).sum := by decide
  have hdescent : baseEnd_360202 < baseStart_360202 := by decide
  rcases family_descends (prefixWord ++ tailWord_360202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360261 : List Nat := [1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_360261 : Nat := 118140960795 + 360261 * 2 ^ 59
def prefixEnd_360261 : Nat := 4983230072969 + 3 ^ 40 * 360261 * 2
def baseEnd_360261 : Nat := 109621957967123087929301

theorem tailTrace_360261 : CollatzResearch.WordTrace tailWord_360261 prefixEnd_360261 109621957967123087929301 := by
  unfold tailWord_360261
  simp only [CollatzResearch.WordTrace]
  refine ⟨13139798147843399525440637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8759865431895599683627091 13139798147843399525440637)
  ·
    refine ⟨4927424305441274822040239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13139798147843399525440637 4927424305441274822040239)
    ·
      refine ⟨7391136458161912233060359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4927424305441274822040239 7391136458161912233060359)
      ·
        refine ⟨11086704687242868349590539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7391136458161912233060359 11086704687242868349590539)
        ·
          refine ⟨16630057030864302524385809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11086704687242868349590539 16630057030864302524385809)
          ·
            refine ⟨12472542773148226893289357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16630057030864302524385809 12472542773148226893289357)
            ·
              refine ⟨4677203539930585084983509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12472542773148226893289357 4677203539930585084983509)
              ·
                refine ⟨109621957967123087929301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4677203539930585084983509 109621957967123087929301)
                ·
                  rfl

theorem cell19_360261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_360261 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360261 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360261 prefixEnd_360261 := by exact prefixLift 360261
  have htrace : WordTrace (prefixWord ++ tailWord_360261) baseStart_360261 baseEnd_360261 := by
    simpa [prefixWord, tailWord_360261, baseEnd_360261] using wordTrace_append hprefix tailTrace_360261
  have hstable : (prefixWord ++ tailWord_360261).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360261).length < 2 ^ (prefixWord ++ tailWord_360261).sum := by decide
  have hdescent : baseEnd_360261 < baseStart_360261 := by decide
  rcases family_descends (prefixWord ++ tailWord_360261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360373 : List Nat := [1, 3, 3, 2, 1, 3, 1, 5]
def baseStart_360373 : Nat := 118140960795 + 360373 * 2 ^ 59
def prefixEnd_360373 : Nat := 4983230072969 + 3 ^ 40 * 360373 * 2
def baseEnd_360373 : Nat := 109656037868340013440107

theorem tailTrace_360373 : CollatzResearch.WordTrace tailWord_360373 prefixEnd_360373 109656037868340013440107 := by
  unfold tailWord_360373
  simp only [CollatzResearch.WordTrace]
  refine ⟨13143883123437642653517773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8762588748958428435678515 13143883123437642653517773)
  ·
    refine ⟨4928956171289115995069165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13143883123437642653517773 4928956171289115995069165)
    ·
      refine ⟨1848358564233418498150937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4928956171289115995069165 1848358564233418498150937)
      ·
        refine ⟨1386268923175063873613203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1848358564233418498150937 1386268923175063873613203)
        ·
          refine ⟨2079403384762595810419805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386268923175063873613203 2079403384762595810419805)
          ·
            refine ⟨779776269285973428907427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2079403384762595810419805 779776269285973428907427)
            ·
              refine ⟨1169664403928960143361141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779776269285973428907427 1169664403928960143361141)
              ·
                refine ⟨109656037868340013440107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1169664403928960143361141 109656037868340013440107)
                ·
                  rfl

theorem cell19_360373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_360373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360373 prefixEnd_360373 := by exact prefixLift 360373
  have htrace : WordTrace (prefixWord ++ tailWord_360373) baseStart_360373 baseEnd_360373 := by
    simpa [prefixWord, tailWord_360373, baseEnd_360373] using wordTrace_append hprefix tailTrace_360373
  have hstable : (prefixWord ++ tailWord_360373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360373).length < 2 ^ (prefixWord ++ tailWord_360373).sum := by decide
  have hdescent : baseEnd_360373 < baseStart_360373 := by decide
  rcases family_descends (prefixWord ++ tailWord_360373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360392 : List Nat := [2, 1, 3, 1, 4, 3, 5]
def baseStart_360392 : Nat := 118140960795 + 360392 * 2 ^ 59
def prefixEnd_360392 : Nat := 4983230072969 + 3 ^ 40 * 360392 * 2
def baseEnd_360392 : Nat := 36553939760051199672611

theorem tailTrace_360392 : CollatzResearch.WordTrace tailWord_360392 prefixEnd_360392 36553939760051199672611 := by
  unfold tailWord_360392
  simp only [CollatzResearch.WordTrace]
  refine ⟨6572288055184404449229715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8763050740245872598972953 6572288055184404449229715)
  ·
    refine ⟨9858432082776606673844573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6572288055184404449229715 9858432082776606673844573)
    ·
      refine ⟨3696912031041227502691715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9858432082776606673844573 3696912031041227502691715)
      ·
        refine ⟨5545368046561841254037573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696912031041227502691715 5545368046561841254037573)
        ·
          refine ⟨1039756508730345235132045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5545368046561841254037573 1039756508730345235132045)
          ·
            refine ⟨389908690773879463174517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1039756508730345235132045 389908690773879463174517)
            ·
              refine ⟨36553939760051199672611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 389908690773879463174517 36553939760051199672611)
              ·
                rfl

theorem cell19_360392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_360392 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360392 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360392 prefixEnd_360392 := by exact prefixLift 360392
  have htrace : WordTrace (prefixWord ++ tailWord_360392) baseStart_360392 baseEnd_360392 := by
    simpa [prefixWord, tailWord_360392, baseEnd_360392] using wordTrace_append hprefix tailTrace_360392
  have hstable : (prefixWord ++ tailWord_360392).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360392).length < 2 ^ (prefixWord ++ tailWord_360392).sum := by decide
  have hdescent : baseEnd_360392 < baseStart_360392 := by decide
  rcases family_descends (prefixWord ++ tailWord_360392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360394 : List Nat := [3, 1, 2, 1, 2, 1, 9]
def baseStart_360394 : Nat := 118140960795 + 360394 * 2 ^ 59
def prefixEnd_360394 : Nat := 4983230072969 + 3 ^ 40 * 360394 * 2
def baseEnd_360394 : Nat := 36554142616606062324461

theorem tailTrace_360394 : CollatzResearch.WordTrace tailWord_360394 prefixEnd_360394 36554142616606062324461 := by
  unfold tailWord_360394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286162264090390810008059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8763099370907708826688157 3286162264090390810008059)
  ·
    refine ⟨4929243396135586215012089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3286162264090390810008059 4929243396135586215012089)
    ·
      refine ⟨3696932547101689661259067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4929243396135586215012089 3696932547101689661259067)
      ·
        refine ⟨5545398820652534491888601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696932547101689661259067 5545398820652534491888601)
        ·
          refine ⟨4159049115489400868916451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5545398820652534491888601 4159049115489400868916451)
          ·
            refine ⟨6238573673234101303374677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159049115489400868916451 6238573673234101303374677)
            ·
              refine ⟨36554142616606062324461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6238573673234101303374677 36554142616606062324461)
              ·
                rfl

theorem cell19_360394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_360394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360394 prefixEnd_360394 := by exact prefixLift 360394
  have htrace : WordTrace (prefixWord ++ tailWord_360394) baseStart_360394 baseEnd_360394 := by
    simpa [prefixWord, tailWord_360394, baseEnd_360394] using wordTrace_append hprefix tailTrace_360394
  have hstable : (prefixWord ++ tailWord_360394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360394).length < 2 ^ (prefixWord ++ tailWord_360394).sum := by decide
  have hdescent : baseEnd_360394 < baseStart_360394 := by decide
  rcases family_descends (prefixWord ++ tailWord_360394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360430 : List Nat := [4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_360430 : Nat := 118140960795 + 360430 * 2 ^ 59
def prefixEnd_360430 : Nat := 4983230072969 + 3 ^ 40 * 360430 * 2
def baseEnd_360430 : Nat := 109673382103780770173285

theorem tailTrace_360430 : CollatzResearch.WordTrace tailWord_360430 prefixEnd_360430 109673382103780770173285 := by
  unfold tailWord_360430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643245260528892673542843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8763974722820760925561829 1643245260528892673542843)
  ·
    refine ⟨2464867890793339010314265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1643245260528892673542843 2464867890793339010314265)
    ·
      refine ⟨1848650918095004257735699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2464867890793339010314265 1848650918095004257735699)
      ·
        refine ⟨2772976377142506386603549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848650918095004257735699 2772976377142506386603549)
        ·
          refine ⟨1039866141428439894976331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2772976377142506386603549 1039866141428439894976331)
          ·
            refine ⟨1559799212142659842464497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039866141428439894976331 1559799212142659842464497)
            ·
              refine ⟨1169849409106994881848373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1559799212142659842464497 1169849409106994881848373)
              ·
                refine ⟨109673382103780770173285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1169849409106994881848373 109673382103780770173285)
                ·
                  rfl

theorem cell19_360430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_360430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360430 prefixEnd_360430 := by exact prefixLift 360430
  have htrace : WordTrace (prefixWord ++ tailWord_360430) baseStart_360430 baseEnd_360430 := by
    simpa [prefixWord, tailWord_360430, baseEnd_360430] using wordTrace_append hprefix tailTrace_360430
  have hstable : (prefixWord ++ tailWord_360430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360430).length < 2 ^ (prefixWord ++ tailWord_360430).sum := by decide
  have hdescent : baseEnd_360430 < baseStart_360430 := by decide
  rcases family_descends (prefixWord ++ tailWord_360430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360432 : List Nat := [2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_360432 : Nat := 118140960795 + 360432 * 2 ^ 59
def prefixEnd_360432 : Nat := 4983230072969 + 3 ^ 40 * 360432 * 2
def baseEnd_360432 : Nat := 109673990673445358128835

theorem tailTrace_360432 : CollatzResearch.WordTrace tailWord_360432 prefixEnd_360432 109673990673445358128835 := by
  unfold tailWord_360432
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573017515111947864957775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8764023353482597153277033 6573017515111947864957775)
  ·
    refine ⟨9859526272667921797436663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6573017515111947864957775 9859526272667921797436663)
    ·
      refine ⟨14789289409001882696154995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9859526272667921797436663 14789289409001882696154995)
      ·
        refine ⟨22183934113502824044232493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14789289409001882696154995 22183934113502824044232493)
        ·
          refine ⟨8318975292563559016587185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22183934113502824044232493 8318975292563559016587185)
          ·
            refine ⟨6239231469422669262440389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8318975292563559016587185 6239231469422669262440389)
            ·
              refine ⟨1169855900516750486707573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6239231469422669262440389 1169855900516750486707573)
              ·
                refine ⟨109673990673445358128835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1169855900516750486707573 109673990673445358128835)
                ·
                  rfl

theorem cell19_360432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_360432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360432 prefixEnd_360432 := by exact prefixLift 360432
  have htrace : WordTrace (prefixWord ++ tailWord_360432) baseStart_360432 baseEnd_360432 := by
    simpa [prefixWord, tailWord_360432, baseEnd_360432] using wordTrace_append hprefix tailTrace_360432
  have hstable : (prefixWord ++ tailWord_360432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360432).length < 2 ^ (prefixWord ++ tailWord_360432).sum := by decide
  have hdescent : baseEnd_360432 < baseStart_360432 := by decide
  rcases family_descends (prefixWord ++ tailWord_360432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360508 : List Nat := [2, 2, 2, 2, 2, 1, 8]
def baseStart_360508 : Nat := 118140960795 + 360508 * 2 ^ 59
def prefixEnd_360508 : Nat := 4983230072969 + 3 ^ 40 * 360508 * 2
def baseEnd_360508 : Nat := 36565705440233233479913

theorem tailTrace_360508 : CollatzResearch.WordTrace tailWord_360508 prefixEnd_360508 36565705440233233479913 := by
  unfold tailWord_360508
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574403488974280354841089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8765871318632373806454785 6574403488974280354841089)
  ·
    refine ⟨4930802616730710266130817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6574403488974280354841089 4930802616730710266130817)
    ·
      refine ⟨3698101962548032699598113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4930802616730710266130817 3698101962548032699598113)
      ·
        refine ⟨2773576471911024524698585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3698101962548032699598113 2773576471911024524698585)
        ·
          refine ⟨2080182353933268393523939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2773576471911024524698585 2080182353933268393523939)
          ·
            refine ⟨3120273530899902590285909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080182353933268393523939 3120273530899902590285909)
            ·
              refine ⟨36565705440233233479913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3120273530899902590285909 36565705440233233479913)
              ·
                rfl

theorem cell19_360508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_360508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360508 prefixEnd_360508 := by exact prefixLift 360508
  have htrace : WordTrace (prefixWord ++ tailWord_360508) baseStart_360508 baseEnd_360508 := by
    simpa [prefixWord, tailWord_360508, baseEnd_360508] using wordTrace_append hprefix tailTrace_360508
  have hstable : (prefixWord ++ tailWord_360508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360508).length < 2 ^ (prefixWord ++ tailWord_360508).sum := by decide
  have hdescent : baseEnd_360508 < baseStart_360508 := by decide
  rcases family_descends (prefixWord ++ tailWord_360508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360525 : List Nat := [1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_360525 : Nat := 118140960795 + 360525 * 2 ^ 59
def prefixEnd_360525 : Nat := 4983230072969 + 3 ^ 40 * 360525 * 2
def baseEnd_360525 : Nat := 109702289162848698061915

theorem tailTrace_360525 : CollatzResearch.WordTrace tailWord_360525 prefixEnd_360525 109702289162848698061915 := by
  unfold tailWord_360525
  simp only [CollatzResearch.WordTrace]
  refine ⟨13149427018886972613051029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8766284679257981742034019 13149427018886972613051029)
  ·
    refine ⟨616379391510326841236767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13149427018886972613051029 616379391510326841236767)
    ·
      refine ⟨924569087265490261855151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 616379391510326841236767 924569087265490261855151)
      ·
        refine ⟨1386853630898235392782727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 924569087265490261855151 1386853630898235392782727)
        ·
          refine ⟨2080280446347353089174091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386853630898235392782727 2080280446347353089174091)
          ·
            refine ⟨3120420669521029633761137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080280446347353089174091 3120420669521029633761137)
            ·
              refine ⟨2340315502140772225320853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120420669521029633761137 2340315502140772225320853)
              ·
                refine ⟨109702289162848698061915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2340315502140772225320853 109702289162848698061915)
                ·
                  rfl

theorem cell19_360525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_360525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360525 prefixEnd_360525 := by exact prefixLift 360525
  have htrace : WordTrace (prefixWord ++ tailWord_360525) baseStart_360525 baseEnd_360525 := by
    simpa [prefixWord, tailWord_360525, baseEnd_360525] using wordTrace_append hprefix tailTrace_360525
  have hstable : (prefixWord ++ tailWord_360525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360525).length < 2 ^ (prefixWord ++ tailWord_360525).sum := by decide
  have hdescent : baseEnd_360525 < baseStart_360525 := by decide
  rcases family_descends (prefixWord ++ tailWord_360525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360544 : List Nat := [2, 1, 1, 3, 2, 3, 4, 3]
def baseStart_360544 : Nat := 118140960795 + 360544 * 2 ^ 59
def prefixEnd_360544 : Nat := 4983230072969 + 3 ^ 40 * 360544 * 2
def baseEnd_360544 : Nat := 109708070574662283639641

theorem tailTrace_360544 : CollatzResearch.WordTrace tailWord_360544 prefixEnd_360544 109708070574662283639641 := by
  unfold tailWord_360544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6575060002909069428996343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8766746670545425905328457 6575060002909069428996343)
  ·
    refine ⟨9862590004363604143494515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6575060002909069428996343 9862590004363604143494515)
    ·
      refine ⟨14793885006545406215241773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9862590004363604143494515 14793885006545406215241773)
      ·
        refine ⟨5547706877454527330715665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14793885006545406215241773 5547706877454527330715665)
        ·
          refine ⟨4160780158090895498036749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5547706877454527330715665 4160780158090895498036749)
          ·
            refine ⟨1560292559284085811763781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4160780158090895498036749 1560292559284085811763781)
            ·
              refine ⟨292554854865766089705709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1560292559284085811763781 292554854865766089705709)
              ·
                refine ⟨109708070574662283639641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292554854865766089705709 109708070574662283639641)
                ·
                  rfl

theorem cell19_360544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_360544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360544 prefixEnd_360544 := by exact prefixLift 360544
  have htrace : WordTrace (prefixWord ++ tailWord_360544) baseStart_360544 baseEnd_360544 := by
    simpa [prefixWord, tailWord_360544, baseEnd_360544] using wordTrace_append hprefix tailTrace_360544
  have hstable : (prefixWord ++ tailWord_360544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360544).length < 2 ^ (prefixWord ++ tailWord_360544).sum := by decide
  have hdescent : baseEnd_360544 < baseStart_360544 := by decide
  rcases family_descends (prefixWord ++ tailWord_360544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360618 : List Nat := [3, 1, 5, 1, 3, 6]
def baseStart_360618 : Nat := 118140960795 + 360618 * 2 ^ 59
def prefixEnd_360618 : Nat := 4983230072969 + 3 ^ 40 * 360618 * 2
def baseEnd_360618 : Nat := 12192287516916893110555

theorem tailTrace_360618 : CollatzResearch.WordTrace tailWord_360618 prefixEnd_360618 12192287516916893110555 := by
  unfold tailWord_360618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3288204751887512374046627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8768546005033366330791005 3288204751887512374046627)
  ·
    refine ⟨4932307127831268561069941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3288204751887512374046627 4932307127831268561069941)
    ·
      refine ⟨462403793234181427600307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4932307127831268561069941 462403793234181427600307)
      ·
        refine ⟨693605689851272141400461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462403793234181427600307 693605689851272141400461)
        ·
          refine ⟨260102133694227053025173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 693605689851272141400461 260102133694227053025173)
          ·
            refine ⟨12192287516916893110555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 260102133694227053025173 12192287516916893110555)
            ·
              rfl

theorem cell19_360618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 6].length) (baseStart_360618 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360618 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360618 prefixEnd_360618 := by exact prefixLift 360618
  have htrace : WordTrace (prefixWord ++ tailWord_360618) baseStart_360618 baseEnd_360618 := by
    simpa [prefixWord, tailWord_360618, baseEnd_360618] using wordTrace_append hprefix tailTrace_360618
  have hstable : (prefixWord ++ tailWord_360618).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360618).length < 2 ^ (prefixWord ++ tailWord_360618).sum := by decide
  have hdescent : baseEnd_360618 < baseStart_360618 := by decide
  rcases family_descends (prefixWord ++ tailWord_360618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360711 : List Nat := [1, 1, 4, 5, 1, 2, 2, 3]
def baseStart_360711 : Nat := 118140960795 + 360711 * 2 ^ 59
def prefixEnd_360711 : Nat := 4983230072969 + 3 ^ 40 * 360711 * 2
def baseEnd_360711 : Nat := 109758886141655377928075

theorem tailTrace_360711 : CollatzResearch.WordTrace tailWord_360711 prefixEnd_360711 109758886141655377928075 := by
  unfold tailWord_360711
  simp only [CollatzResearch.WordTrace]
  refine ⟨13156210996213126379321987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8770807330808750919547991 13156210996213126379321987)
  ·
    refine ⟨19734316494319689568982981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13156210996213126379321987 19734316494319689568982981)
    ·
      refine ⟨3700184342684941794184309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19734316494319689568982981 3700184342684941794184309)
      ·
        refine ⟨346892282126713293204779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3700184342684941794184309 346892282126713293204779)
        ·
          refine ⟨520338423190069939807169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346892282126713293204779 520338423190069939807169)
          ·
            refine ⟨390253817392552454855377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520338423190069939807169 390253817392552454855377)
            ·
              refine ⟨292690363044414341141533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390253817392552454855377 292690363044414341141533)
              ·
                refine ⟨109758886141655377928075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292690363044414341141533 109758886141655377928075)
                ·
                  rfl

theorem cell19_360711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_360711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360711 prefixEnd_360711 := by exact prefixLift 360711
  have htrace : WordTrace (prefixWord ++ tailWord_360711) baseStart_360711 baseEnd_360711 := by
    simpa [prefixWord, tailWord_360711, baseEnd_360711] using wordTrace_append hprefix tailTrace_360711
  have hstable : (prefixWord ++ tailWord_360711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360711).length < 2 ^ (prefixWord ++ tailWord_360711).sum := by decide
  have hdescent : baseEnd_360711 < baseStart_360711 := by decide
  rcases family_descends (prefixWord ++ tailWord_360711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360736 : List Nat := [2, 1, 1, 5, 2, 1, 7]
def baseStart_360736 : Nat := 118140960795 + 360736 * 2 ^ 59
def prefixEnd_360736 : Nat := 4983230072969 + 3 ^ 40 * 360736 * 2
def baseEnd_360736 : Nat := 36588831087487575790817

theorem tailTrace_360736 : CollatzResearch.WordTrace tailWord_360736 prefixEnd_360736 36588831087487575790817 := by
  unfold tailWord_360736
  simp only [CollatzResearch.WordTrace]
  refine ⟨6578561410561277824491031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8771415214081703765988041 6578561410561277824491031)
  ·
    refine ⟨9867842115841916736736547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6578561410561277824491031 9867842115841916736736547)
    ·
      refine ⟨14801763173762875105104821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9867842115841916736736547 14801763173762875105104821)
      ·
        refine ⟨1387665297540269541103577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14801763173762875105104821 1387665297540269541103577)
        ·
          refine ⟨1040748973155202155827683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1387665297540269541103577 1040748973155202155827683)
          ·
            refine ⟨1561123459732803233741525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040748973155202155827683 1561123459732803233741525)
            ·
              refine ⟨36588831087487575790817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1561123459732803233741525 36588831087487575790817)
              ·
                rfl

theorem cell19_360736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_360736 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360736 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360736 prefixEnd_360736 := by exact prefixLift 360736
  have htrace : WordTrace (prefixWord ++ tailWord_360736) baseStart_360736 baseEnd_360736 := by
    simpa [prefixWord, tailWord_360736, baseEnd_360736] using wordTrace_append hprefix tailTrace_360736
  have hstable : (prefixWord ++ tailWord_360736).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360736).length < 2 ^ (prefixWord ++ tailWord_360736).sum := by decide
  have hdescent : baseEnd_360736 < baseStart_360736 := by decide
  rcases family_descends (prefixWord ++ tailWord_360736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360753 : List Nat := [1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_360753 : Nat := 118140960795 + 360753 * 2 ^ 59
def prefixEnd_360753 : Nat := 4983230072969 + 3 ^ 40 * 360753 * 2
def baseEnd_360753 : Nat := 109771666104611724994627

theorem tailTrace_360753 : CollatzResearch.WordTrace tailWord_360753 prefixEnd_360753 109771666104611724994627 := by
  unfold tailWord_360753
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157742862060967552350913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8771828574707311701567275 13157742862060967552350913)
  ·
    refine ⟨9868307146545725664263185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13157742862060967552350913 9868307146545725664263185)
    ·
      refine ⟨7401230359909294248197389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9868307146545725664263185 7401230359909294248197389)
      ·
        refine ⟨2775461384965985343074021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7401230359909294248197389 2775461384965985343074021)
        ·
          refine ⟨520399009681122251826379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2775461384965985343074021 520399009681122251826379)
          ·
            refine ⟨780598514521683377739569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520399009681122251826379 780598514521683377739569)
            ·
              refine ⟨585448885891262533304677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 780598514521683377739569 585448885891262533304677)
              ·
                refine ⟨109771666104611724994627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585448885891262533304677 109771666104611724994627)
                ·
                  rfl

theorem cell19_360753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_360753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360753 prefixEnd_360753 := by exact prefixLift 360753
  have htrace : WordTrace (prefixWord ++ tailWord_360753) baseStart_360753 baseEnd_360753 := by
    simpa [prefixWord, tailWord_360753, baseEnd_360753] using wordTrace_append hprefix tailTrace_360753
  have hstable : (prefixWord ++ tailWord_360753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360753).length < 2 ^ (prefixWord ++ tailWord_360753).sum := by decide
  have hdescent : baseEnd_360753 < baseStart_360753 := by decide
  rcases family_descends (prefixWord ++ tailWord_360753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360755 : List Nat := [1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_360755 : Nat := 118140960795 + 360755 * 2 ^ 59
def prefixEnd_360755 : Nat := 4983230072969 + 3 ^ 40 * 360755 * 2
def baseEnd_360755 : Nat := 109772274674276312950177

theorem tailTrace_360755 : CollatzResearch.WordTrace tailWord_360755 prefixEnd_360755 109772274674276312950177 := by
  unfold tailWord_360755
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157815808053721893923719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8771877205369147929282479 13157815808053721893923719)
  ·
    refine ⟨19736723712080582840885579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13157815808053721893923719 19736723712080582840885579)
    ·
      refine ⟨29605085568120874261328369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19736723712080582840885579 29605085568120874261328369)
      ·
        refine ⟨22203814176090655695996277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29605085568120874261328369 22203814176090655695996277)
        ·
          refine ⟨2081607579008498971499651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22203814176090655695996277 2081607579008498971499651)
          ·
            refine ⟨3122411368512748457249477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081607579008498971499651 3122411368512748457249477)
            ·
              refine ⟨585452131596140335734277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3122411368512748457249477 585452131596140335734277)
              ·
                refine ⟨109772274674276312950177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585452131596140335734277 109772274674276312950177)
                ·
                  rfl

theorem cell19_360755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_360755 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360755 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360755 prefixEnd_360755 := by exact prefixLift 360755
  have htrace : WordTrace (prefixWord ++ tailWord_360755) baseStart_360755 baseEnd_360755 := by
    simpa [prefixWord, tailWord_360755, baseEnd_360755] using wordTrace_append hprefix tailTrace_360755
  have hstable : (prefixWord ++ tailWord_360755).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360755).length < 2 ^ (prefixWord ++ tailWord_360755).sum := by decide
  have hdescent : baseEnd_360755 < baseStart_360755 := by decide
  rcases family_descends (prefixWord ++ tailWord_360755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360810 : List Nat := [3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_360810 : Nat := 118140960795 + 360810 * 2 ^ 59
def prefixEnd_360810 : Nat := 4983230072969 + 3 ^ 40 * 360810 * 2
def baseEnd_360810 : Nat := 109789010340052481727805

theorem tailTrace_360810 : CollatzResearch.WordTrace tailWord_360810 prefixEnd_360810 109789010340052481727805 := by
  unfold tailWord_360810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3289955455713616571793971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8773214548569644191450589 3289955455713616571793971)
  ·
    refine ⟨4934933183570424857690957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3289955455713616571793971 4934933183570424857690957)
    ·
      refine ⟨1850599943838909321634109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4934933183570424857690957 1850599943838909321634109)
      ·
        refine ⟨693974978939590995612791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1850599943838909321634109 693974978939590995612791)
        ·
          refine ⟨1040962468409386493419187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693974978939590995612791 1040962468409386493419187)
          ·
            refine ⟨1561443702614079740128781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040962468409386493419187 1561443702614079740128781)
            ·
              refine ⟨585541388480279902548293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1561443702614079740128781 585541388480279902548293)
              ·
                refine ⟨109789010340052481727805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 585541388480279902548293 109789010340052481727805)
                ·
                  rfl

theorem cell19_360810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_360810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360810 prefixEnd_360810 := by exact prefixLift 360810
  have htrace : WordTrace (prefixWord ++ tailWord_360810) baseStart_360810 baseEnd_360810 := by
    simpa [prefixWord, tailWord_360810, baseEnd_360810] using wordTrace_append hprefix tailTrace_360810
  have hstable : (prefixWord ++ tailWord_360810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360810).length < 2 ^ (prefixWord ++ tailWord_360810).sum := by decide
  have hdescent : baseEnd_360810 < baseStart_360810 := by decide
  rcases family_descends (prefixWord ++ tailWord_360810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360829 : List Nat := [1, 4, 1, 1, 2, 4, 3, 3]
def baseStart_360829 : Nat := 118140960795 + 360829 * 2 ^ 59
def prefixEnd_360829 : Nat := 4983230072969 + 3 ^ 40 * 360829 * 2
def baseEnd_360829 : Nat := 109794791751866067305531

theorem tailTrace_360829 : CollatzResearch.WordTrace tailWord_360829 prefixEnd_360829 109794791751866067305531 := by
  unfold tailWord_360829
  simp only [CollatzResearch.WordTrace]
  refine ⟨13160514809785632532117541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8773676539857088354745027 13160514809785632532117541)
  ·
    refine ⟨2467596526834806099772039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13160514809785632532117541 2467596526834806099772039)
    ·
      refine ⟨3701394790252209149658059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2467596526834806099772039 3701394790252209149658059)
      ·
        refine ⟨5552092185378313724487089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3701394790252209149658059 5552092185378313724487089)
        ·
          refine ⟨4164069139033735293365317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5552092185378313724487089 4164069139033735293365317)
          ·
            refine ⟨780762963568825367505997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4164069139033735293365317 780762963568825367505997)
            ·
              refine ⟨292786111338309512814749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780762963568825367505997 292786111338309512814749)
              ·
                refine ⟨109794791751866067305531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292786111338309512814749 109794791751866067305531)
                ·
                  rfl

theorem cell19_360829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_360829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360829 prefixEnd_360829 := by exact prefixLift 360829
  have htrace : WordTrace (prefixWord ++ tailWord_360829) baseStart_360829 baseEnd_360829 := by
    simpa [prefixWord, tailWord_360829, baseEnd_360829] using wordTrace_append hprefix tailTrace_360829
  have hstable : (prefixWord ++ tailWord_360829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360829).length < 2 ^ (prefixWord ++ tailWord_360829).sum := by decide
  have hdescent : baseEnd_360829 < baseStart_360829 := by decide
  rcases family_descends (prefixWord ++ tailWord_360829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360947 : List Nat := [1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_360947 : Nat := 118140960795 + 360947 * 2 ^ 59
def prefixEnd_360947 : Nat := 4983230072969 + 3 ^ 40 * 360947 * 2
def baseEnd_360947 : Nat := 109830697362076756682987

theorem tailTrace_360947 : CollatzResearch.WordTrace tailWord_360947 prefixEnd_360947 109830697362076756682987 := by
  unfold tailWord_360947
  simp only [CollatzResearch.WordTrace]
  refine ⟨13164818623358138684913095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8776545748905425789942063 13164818623358138684913095)
  ·
    refine ⟨19747227935037208027369643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13164818623358138684913095 19747227935037208027369643)
    ·
      refine ⟨29620841902555812041054465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19747227935037208027369643 29620841902555812041054465)
      ·
        refine ⟨22215631426916859030790849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29620841902555812041054465 22215631426916859030790849)
        ·
          refine ⟨16661723570187644273093137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22215631426916859030790849 16661723570187644273093137)
          ·
            refine ⟨12496292677640733204819853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16661723570187644273093137 12496292677640733204819853)
            ·
              refine ⟨4686109754115274951807445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12496292677640733204819853 4686109754115274951807445)
              ·
                refine ⟨109830697362076756682987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4686109754115274951807445 109830697362076756682987)
                ·
                  rfl

theorem cell19_360947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_360947 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360947 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360947 prefixEnd_360947 := by exact prefixLift 360947
  have htrace : WordTrace (prefixWord ++ tailWord_360947) baseStart_360947 baseEnd_360947 := by
    simpa [prefixWord, tailWord_360947, baseEnd_360947] using wordTrace_append hprefix tailTrace_360947
  have hstable : (prefixWord ++ tailWord_360947).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360947).length < 2 ^ (prefixWord ++ tailWord_360947).sum := by decide
  have hdescent : baseEnd_360947 < baseStart_360947 := by decide
  rcases family_descends (prefixWord ++ tailWord_360947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360962 : List Nat := [3, 4, 1, 2, 2, 7]
def baseStart_360962 : Nat := 118140960795 + 360962 * 2 ^ 59
def prefixEnd_360962 : Nat := 4983230072969 + 3 ^ 40 * 360962 * 2
def baseEnd_360962 : Nat := 12203917959395685149957

theorem tailTrace_360962 : CollatzResearch.WordTrace tailWord_360962 prefixEnd_360962 12203917959395685149957 := by
  unfold tailWord_360962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3291341429575949061677285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8776910478869197497806093 3291341429575949061677285)
  ·
    refine ⟨617126518045490449064491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3291341429575949061677285 617126518045490449064491)
    ·
      refine ⟨925689777068235673596737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 617126518045490449064491 925689777068235673596737)
      ·
        refine ⟨694267332801176755197553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 925689777068235673596737 694267332801176755197553)
        ·
          refine ⟨520700499600882566398165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694267332801176755197553 520700499600882566398165)
          ·
            refine ⟨12203917959395685149957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 520700499600882566398165 12203917959395685149957)
            ·
              rfl

theorem cell19_360962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 7].length) (baseStart_360962 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360962 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360962 prefixEnd_360962 := by exact prefixLift 360962
  have htrace : WordTrace (prefixWord ++ tailWord_360962) baseStart_360962 baseEnd_360962 := by
    simpa [prefixWord, tailWord_360962, baseEnd_360962] using wordTrace_append hprefix tailTrace_360962
  have hstable : (prefixWord ++ tailWord_360962).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360962).length < 2 ^ (prefixWord ++ tailWord_360962).sum := by decide
  have hdescent : baseEnd_360962 < baseStart_360962 := by decide
  rcases family_descends (prefixWord ++ tailWord_360962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360964 : List Nat := [2, 3, 2, 3, 1, 8]
def baseStart_360964 : Nat := 118140960795 + 360964 * 2 ^ 59
def prefixEnd_360964 : Nat := 4983230072969 + 3 ^ 40 * 360964 * 2
def baseEnd_360964 : Nat := 12203985578247306033907

theorem tailTrace_360964 : CollatzResearch.WordTrace tailWord_360964 prefixEnd_360964 12203985578247306033907 := by
  unfold tailWord_360964
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582719332148275294140973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8776959109531033725521297 6582719332148275294140973)
  ·
    refine ⟨2468519749555603235302865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6582719332148275294140973 2468519749555603235302865)
    ·
      refine ⟨1851389812166702426477149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2468519749555603235302865 1851389812166702426477149)
      ·
        refine ⟨694271179562513409928931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1851389812166702426477149 694271179562513409928931)
        ·
          refine ⟨1041406769343770114893397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694271179562513409928931 1041406769343770114893397)
          ·
            refine ⟨12203985578247306033907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1041406769343770114893397 12203985578247306033907)
            ·
              rfl

theorem cell19_360964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 8].length) (baseStart_360964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_360964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_360964 prefixEnd_360964 := by exact prefixLift 360964
  have htrace : WordTrace (prefixWord ++ tailWord_360964) baseStart_360964 baseEnd_360964 := by
    simpa [prefixWord, tailWord_360964, baseEnd_360964] using wordTrace_append hprefix tailTrace_360964
  have hstable : (prefixWord ++ tailWord_360964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360964).length < 2 ^ (prefixWord ++ tailWord_360964).sum := by decide
  have hdescent : baseEnd_360964 < baseStart_360964 := by decide
  rcases family_descends (prefixWord ++ tailWord_360964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361004 : List Nat := [2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_361004 : Nat := 118140960795 + 361004 * 2 ^ 59
def prefixEnd_361004 : Nat := 4983230072969 + 3 ^ 40 * 361004 * 2
def baseEnd_361004 : Nat := 109848041597517513416165

theorem tailTrace_361004 : CollatzResearch.WordTrace tailWord_361004 prefixEnd_361004 109848041597517513416165 := by
  unfold tailWord_361004
  simp only [CollatzResearch.WordTrace]
  refine ⟨6583448792075818709869033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8777931722767758279825377 6583448792075818709869033)
  ·
    refine ⟨4937586594056864032401775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6583448792075818709869033 4937586594056864032401775)
    ·
      refine ⟨7406379891085296048602663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4937586594056864032401775 7406379891085296048602663)
      ·
        refine ⟨11109569836627944072903995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7406379891085296048602663 11109569836627944072903995)
        ·
          refine ⟨16664354754941916109355993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11109569836627944072903995 16664354754941916109355993)
          ·
            refine ⟨12498266066206437082016995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16664354754941916109355993 12498266066206437082016995)
            ·
              refine ⟨18747399099309655623025493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12498266066206437082016995 18747399099309655623025493)
              ·
                refine ⟨109848041597517513416165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18747399099309655623025493 109848041597517513416165)
                ·
                  rfl

theorem cell19_361004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_361004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361004 prefixEnd_361004 := by exact prefixLift 361004
  have htrace : WordTrace (prefixWord ++ tailWord_361004) baseStart_361004 baseEnd_361004 := by
    simpa [prefixWord, tailWord_361004, baseEnd_361004] using wordTrace_append hprefix tailTrace_361004
  have hstable : (prefixWord ++ tailWord_361004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361004).length < 2 ^ (prefixWord ++ tailWord_361004).sum := by decide
  have hdescent : baseEnd_361004 < baseStart_361004 := by decide
  rcases family_descends (prefixWord ++ tailWord_361004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361021 : List Nat := [1, 4, 1, 3, 2, 2, 6]
def baseStart_361021 : Nat := 118140960795 + 361021 * 2 ^ 59
def prefixEnd_361021 : Nat := 4983230072969 + 3 ^ 40 * 361021 * 2
def baseEnd_361021 : Nat := 36617738146555503679447

theorem tailTrace_361021 : CollatzResearch.WordTrace tailWord_361021 prefixEnd_361021 36617738146555503679447 := by
  unfold tailWord_361021
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167517625090049323106917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8778345083393366215404611 13167517625090049323106917)
  ·
    refine ⟨2468909554704384248082547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13167517625090049323106917 2468909554704384248082547)
    ·
      refine ⟨3703364332056576372123821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2468909554704384248082547 3703364332056576372123821)
      ·
        refine ⟨1388761624521216139546433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3703364332056576372123821 1388761624521216139546433)
        ·
          refine ⟨1041571218390912104659825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1388761624521216139546433 1041571218390912104659825)
          ·
            refine ⟨781178413793184078494869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1041571218390912104659825 781178413793184078494869)
            ·
              refine ⟨36617738146555503679447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 781178413793184078494869 36617738146555503679447)
              ·
                rfl

theorem cell19_361021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_361021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361021 prefixEnd_361021 := by exact prefixLift 361021
  have htrace : WordTrace (prefixWord ++ tailWord_361021) baseStart_361021 baseEnd_361021 := by
    simpa [prefixWord, tailWord_361021, baseEnd_361021] using wordTrace_append hprefix tailTrace_361021
  have hstable : (prefixWord ++ tailWord_361021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361021).length < 2 ^ (prefixWord ++ tailWord_361021).sum := by decide
  have hdescent : baseEnd_361021 < baseStart_361021 := by decide
  rcases family_descends (prefixWord ++ tailWord_361021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361023 : List Nat := [1, 1, 2, 2, 3, 2, 8]
def baseStart_361023 : Nat := 118140960795 + 361023 * 2 ^ 59
def prefixEnd_361023 : Nat := 4983230072969 + 3 ^ 40 * 361023 * 2
def baseEnd_361023 : Nat := 36617941003110366331297

theorem tailTrace_361023 : CollatzResearch.WordTrace tailWord_361023 prefixEnd_361023 36617941003110366331297 := by
  unfold tailWord_361023
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167590571082803664679723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8778393714055202443119815 13167590571082803664679723)
  ·
    refine ⟨19751385856624205497019585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13167590571082803664679723 19751385856624205497019585)
    ·
      refine ⟨14813539392468154122764689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19751385856624205497019585 14813539392468154122764689)
      ·
        refine ⟨11110154544351115592073517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14813539392468154122764689 11110154544351115592073517)
        ·
          refine ⟨4166307954131668347027569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11110154544351115592073517 4166307954131668347027569)
          ·
            refine ⟨3124730965598751260270677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4166307954131668347027569 3124730965598751260270677)
            ·
              refine ⟨36617941003110366331297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3124730965598751260270677 36617941003110366331297)
              ·
                rfl

theorem cell19_361023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_361023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361023 prefixEnd_361023 := by exact prefixLift 361023
  have htrace : WordTrace (prefixWord ++ tailWord_361023) baseStart_361023 baseEnd_361023 := by
    simpa [prefixWord, tailWord_361023, baseEnd_361023] using wordTrace_append hprefix tailTrace_361023
  have hstable : (prefixWord ++ tailWord_361023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361023).length < 2 ^ (prefixWord ++ tailWord_361023).sum := by decide
  have hdescent : baseEnd_361023 < baseStart_361023 := by decide
  rcases family_descends (prefixWord ++ tailWord_361023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361057 : List Nat := [1, 2, 3, 1, 1, 6, 2, 3]
def baseStart_361057 : Nat := 118140960795 + 361057 * 2 ^ 59
def prefixEnd_361057 : Nat := 4983230072969 + 3 ^ 40 * 361057 * 2
def baseEnd_361057 : Nat := 109864168693629094238243

theorem tailTrace_361057 : CollatzResearch.WordTrace tailWord_361057 prefixEnd_361057 109864168693629094238243 := by
  unfold tailWord_361057
  simp only [CollatzResearch.WordTrace]
  refine ⟨13168830652959627471417425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8779220435306418314278283 13168830652959627471417425)
  ·
    refine ⟨9876622989719720603563069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13168830652959627471417425 9876622989719720603563069)
    ·
      refine ⟨3703733621144895226336151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9876622989719720603563069 3703733621144895226336151)
      ·
        refine ⟨5555600431717342839504227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3703733621144895226336151 5555600431717342839504227)
        ·
          refine ⟨8333400647576014259256341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555600431717342839504227 8333400647576014259256341)
          ·
            refine ⟨390628155355125668402641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8333400647576014259256341 390628155355125668402641)
            ·
              refine ⟨292971116516344251301981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390628155355125668402641 292971116516344251301981)
              ·
                refine ⟨109864168693629094238243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292971116516344251301981 109864168693629094238243)
                ·
                  rfl

theorem cell19_361057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_361057 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361057 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361057 prefixEnd_361057 := by exact prefixLift 361057
  have htrace : WordTrace (prefixWord ++ tailWord_361057) baseStart_361057 baseEnd_361057 := by
    simpa [prefixWord, tailWord_361057, baseEnd_361057] using wordTrace_append hprefix tailTrace_361057
  have hstable : (prefixWord ++ tailWord_361057).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361057).length < 2 ^ (prefixWord ++ tailWord_361057).sum := by decide
  have hdescent : baseEnd_361057 < baseStart_361057 := by decide
  rcases family_descends (prefixWord ++ tailWord_361057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361116 : List Nat := [2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_361116 : Nat := 118140960795 + 361116 * 2 ^ 59
def prefixEnd_361116 : Nat := 4983230072969 + 3 ^ 40 * 361116 * 2
def baseEnd_361116 : Nat := 109882121498734438926971

theorem tailTrace_361116 : CollatzResearch.WordTrace tailWord_361116 prefixEnd_361116 109882121498734438926971 := by
  unfold tailWord_361116
  simp only [CollatzResearch.WordTrace]
  refine ⟨6585491279872940273907601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8780655039830587031876801 6585491279872940273907601)
  ·
    refine ⟨4939118459904705205430701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6585491279872940273907601 4939118459904705205430701)
    ·
      refine ⟨1852169422464264452036513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4939118459904705205430701 1852169422464264452036513)
      ·
        refine ⟨1389127066848198339027385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1852169422464264452036513 1389127066848198339027385)
        ·
          refine ⟨1041845300136148754270539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1389127066848198339027385 1041845300136148754270539)
          ·
            refine ⟨1562767950204223131405809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041845300136148754270539 1562767950204223131405809)
            ·
              refine ⟨1172075962653167348554357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562767950204223131405809 1172075962653167348554357)
              ·
                refine ⟨109882121498734438926971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1172075962653167348554357 109882121498734438926971)
                ·
                  rfl

theorem cell19_361116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_361116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361116 prefixEnd_361116 := by exact prefixLift 361116
  have htrace : WordTrace (prefixWord ++ tailWord_361116) baseStart_361116 baseEnd_361116 := by
    simpa [prefixWord, tailWord_361116, baseEnd_361116] using wordTrace_append hprefix tailTrace_361116
  have hstable : (prefixWord ++ tailWord_361116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361116).length < 2 ^ (prefixWord ++ tailWord_361116).sum := by decide
  have hdescent : baseEnd_361116 < baseStart_361116 := by decide
  rcases family_descends (prefixWord ++ tailWord_361116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361192 : List Nat := [2, 1, 4, 1, 4, 1, 6]
def baseStart_361192 : Nat := 118140960795 + 361192 * 2 ^ 59
def prefixEnd_361192 : Nat := 4983230072969 + 3 ^ 40 * 361192 * 2
def baseEnd_361192 : Nat := 36635082381996260412625

theorem tailTrace_361192 : CollatzResearch.WordTrace tailWord_361192 prefixEnd_361192 36635082381996260412625 := by
  unfold tailWord_361192
  simp only [CollatzResearch.WordTrace]
  refine ⟨6586877253735272763790915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8782503004980363685054553 6586877253735272763790915)
  ·
    refine ⟨9880315880602909145686373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6586877253735272763790915 9880315880602909145686373)
    ·
      refine ⟨1852559227613045464816195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9880315880602909145686373 1852559227613045464816195)
      ·
        refine ⟨2778838841419568197224293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852559227613045464816195 2778838841419568197224293)
        ·
          refine ⟨521032282766169036979555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2778838841419568197224293 521032282766169036979555)
          ·
            refine ⟨781548424149253555469333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521032282766169036979555 781548424149253555469333)
            ·
              refine ⟨36635082381996260412625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 781548424149253555469333 36635082381996260412625)
              ·
                rfl

theorem cell19_361192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_361192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_361192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_361192 prefixEnd_361192 := by exact prefixLift 361192
  have htrace : WordTrace (prefixWord ++ tailWord_361192) baseStart_361192 baseEnd_361192 := by
    simpa [prefixWord, tailWord_361192, baseEnd_361192] using wordTrace_append hprefix tailTrace_361192
  have hstable : (prefixWord ++ tailWord_361192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361192).length < 2 ^ (prefixWord ++ tailWord_361192).sum := by decide
  have hdescent : baseEnd_361192 < baseStart_361192 := by decide
  rcases family_descends (prefixWord ++ tailWord_361192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
