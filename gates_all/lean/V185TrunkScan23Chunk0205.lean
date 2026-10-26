import V185TrunkScan23Chunk0204

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1213036 : List Nat := [2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 3]
def baseStart_1213036 : Nat := 118140960795 + 1213036 * 2 ^ 59
def prefixEnd_1213036 : Nat := 4983230072969 + 3 ^ 40 * 1213036 * 2
def baseEnd_1213036 : Nat := 622870519207421224771355

theorem tailTrace_1213036 : CollatzResearch.WordTrace tailWord_1213036 prefixEnd_1213036 622870519207421224771355 := by
  unfold tailWord_1213036
  simp only [CollatzResearch.WordTrace]
  refine ⟨22121528816692608450129481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29495371755590144600172641 22121528816692608450129481)
  ·
    refine ⟨16591146612519456337597111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22121528816692608450129481 16591146612519456337597111)
    ·
      refine ⟨24886719918779184506395667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16591146612519456337597111 24886719918779184506395667)
      ·
        refine ⟨37330079878168776759593501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24886719918779184506395667 37330079878168776759593501)
        ·
          refine ⟨13998779954313291284847563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37330079878168776759593501 13998779954313291284847563)
          ·
            refine ⟨20998169931469936927271345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13998779954313291284847563 20998169931469936927271345)
            ·
              refine ⟨15748627448602452695453509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20998169931469936927271345 15748627448602452695453509)
              ·
                refine ⟨2952867646612959880397533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15748627448602452695453509 2952867646612959880397533)
                ·
                  refine ⟨1107325367479859955149075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2952867646612959880397533 1107325367479859955149075)
                  ·
                    refine ⟨1660988051219789932723613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1107325367479859955149075 1660988051219789932723613)
                    ·
                      refine ⟨622870519207421224771355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1660988051219789932723613 622870519207421224771355)
                      ·
                        rfl

theorem cell23_1213036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_1213036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213036 prefixEnd_1213036 := by exact prefixLift 1213036
  have htrace : WordTrace (prefixWord ++ tailWord_1213036) baseStart_1213036 baseEnd_1213036 := by
    simpa [prefixWord, tailWord_1213036, baseEnd_1213036] using wordTrace_append hprefix tailTrace_1213036
  have hstable : (prefixWord ++ tailWord_1213036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213036).length < 2 ^ (prefixWord ++ tailWord_1213036).sum := by decide
  have hdescent : baseEnd_1213036 < baseStart_1213036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213070 : List Nat := [4, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3]
def baseStart_1213070 : Nat := 118140960795 + 1213070 * 2 ^ 59
def prefixEnd_1213070 : Nat := 4983230072969 + 3 ^ 40 * 1213070 * 2
def baseEnd_1213070 : Nat := 622887977549674091746199

theorem tailTrace_1213070 : CollatzResearch.WordTrace tailWord_1213070 prefixEnd_1213070 622887977549674091746199 := by
  unfold tailWord_1213070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5530537214407755088374583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29496198476841360471331109 5530537214407755088374583)
  ·
    refine ⟨8295805821611632632561875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5530537214407755088374583 8295805821611632632561875)
    ·
      refine ⟨12443708732417448948842813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8295805821611632632561875 12443708732417448948842813)
      ·
        refine ⟨4666390774656543355816055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12443708732417448948842813 4666390774656543355816055)
        ·
          refine ⟨6999586161984815033724083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4666390774656543355816055 6999586161984815033724083)
          ·
            refine ⟨10499379242977222550586125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6999586161984815033724083 10499379242977222550586125)
            ·
              refine ⟨3937267216116458456469797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10499379242977222550586125 3937267216116458456469797)
              ·
                refine ⟨738237603021835960588087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3937267216116458456469797 738237603021835960588087)
                ·
                  refine ⟨1107356404532753940882131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738237603021835960588087 1107356404532753940882131)
                  ·
                    refine ⟨1661034606799130911323197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1107356404532753940882131 1661034606799130911323197)
                    ·
                      refine ⟨622887977549674091746199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1661034606799130911323197 622887977549674091746199)
                      ·
                        rfl

theorem cell23_1213070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_1213070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213070 prefixEnd_1213070 := by exact prefixLift 1213070
  have htrace : WordTrace (prefixWord ++ tailWord_1213070) baseStart_1213070 baseEnd_1213070 := by
    simpa [prefixWord, tailWord_1213070, baseEnd_1213070] using wordTrace_append hprefix tailTrace_1213070
  have hstable : (prefixWord ++ tailWord_1213070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213070).length < 2 ^ (prefixWord ++ tailWord_1213070).sum := by decide
  have hdescent : baseEnd_1213070 < baseStart_1213070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213079 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1213079 : Nat := 118140960795 + 1213079 * 2 ^ 59
def prefixEnd_1213079 : Nat := 4983230072969 + 3 ^ 40 * 1213079 * 2
def baseEnd_1213079 : Nat := 622892598875564556533657

theorem tailTrace_1213079 : CollatzResearch.WordTrace tailWord_1213079 prefixEnd_1213079 622892598875564556533657 := by
  unfold tailWord_1213079
  simp only [CollatzResearch.WordTrace]
  refine ⟨44244625972229435244074291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29496417314819623496049527 44244625972229435244074291)
  ·
    refine ⟨66366938958344152866111437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44244625972229435244074291 66366938958344152866111437)
    ·
      refine ⟨24887602109379057324791789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66366938958344152866111437 24887602109379057324791789)
      ·
        refine ⟨9332850791017146496796921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24887602109379057324791789 9332850791017146496796921)
        ·
          refine ⟨6999638093262859872597691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9332850791017146496796921 6999638093262859872597691)
          ·
            refine ⟨10499457139894289808896537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6999638093262859872597691 10499457139894289808896537)
            ·
              refine ⟨7874592854920717356672403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10499457139894289808896537 7874592854920717356672403)
              ·
                refine ⟨11811889282381076035008605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7874592854920717356672403 11811889282381076035008605)
                ·
                  refine ⟨4429458480892903513128227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11811889282381076035008605 4429458480892903513128227)
                  ·
                    refine ⟨6644187721339355269692341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4429458480892903513128227 6644187721339355269692341)
                    ·
                      refine ⟨622892598875564556533657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6644187721339355269692341 622892598875564556533657)
                      ·
                        rfl

theorem cell23_1213079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1213079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213079 prefixEnd_1213079 := by exact prefixLift 1213079
  have htrace : WordTrace (prefixWord ++ tailWord_1213079) baseStart_1213079 baseEnd_1213079 := by
    simpa [prefixWord, tailWord_1213079, baseEnd_1213079] using wordTrace_append hprefix tailTrace_1213079
  have hstable : (prefixWord ++ tailWord_1213079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213079).length < 2 ^ (prefixWord ++ tailWord_1213079).sum := by decide
  have hdescent : baseEnd_1213079 < baseStart_1213079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213140 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1213140 : Nat := 118140960795 + 1213140 * 2 ^ 59
def prefixEnd_1213140 : Nat := 4983230072969 + 3 ^ 40 * 1213140 * 2
def baseEnd_1213140 : Nat := 622923921195488817870877

theorem tailTrace_1213140 : CollatzResearch.WordTrace tailWord_1213140 prefixEnd_1213140 622923921195488817870877 := by
  unfold tailWord_1213140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22123425412504221331022437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29497900550005628441363249 22123425412504221331022437)
  ·
    refine ⟨4148142264844541499566707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22123425412504221331022437 4148142264844541499566707)
    ·
      refine ⟨6222213397266812249350061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4148142264844541499566707 6222213397266812249350061)
      ·
        refine ⟨2333330023975054593506273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6222213397266812249350061 2333330023975054593506273)
        ·
          refine ⟨1749997517981290945129705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2333330023975054593506273 1749997517981290945129705)
          ·
            refine ⟨1312498138485968208847279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1749997517981290945129705 1312498138485968208847279)
            ·
              refine ⟨1968747207728952313270919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312498138485968208847279 1968747207728952313270919)
              ·
                refine ⟨2953120811593428469906379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968747207728952313270919 2953120811593428469906379)
                ·
                  refine ⟨4429681217390142704859569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953120811593428469906379 4429681217390142704859569)
                  ·
                    refine ⟨3322260913042607028644677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4429681217390142704859569 3322260913042607028644677)
                    ·
                      refine ⟨622923921195488817870877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3322260913042607028644677 622923921195488817870877)
                      ·
                        rfl

theorem cell23_1213140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1213140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213140 prefixEnd_1213140 := by exact prefixLift 1213140
  have htrace : WordTrace (prefixWord ++ tailWord_1213140) baseStart_1213140 baseEnd_1213140 := by
    simpa [prefixWord, tailWord_1213140, baseEnd_1213140] using wordTrace_append hprefix tailTrace_1213140
  have hstable : (prefixWord ++ tailWord_1213140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213140).length < 2 ^ (prefixWord ++ tailWord_1213140).sum := by decide
  have hdescent : baseEnd_1213140 < baseStart_1213140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213143 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 3]
def baseStart_1213143 : Nat := 118140960795 + 1213143 * 2 ^ 59
def prefixEnd_1213143 : Nat := 4983230072969 + 3 ^ 40 * 1213143 * 2
def baseEnd_1213143 : Nat := 622925461637452306133363

theorem tailTrace_1213143 : CollatzResearch.WordTrace tailWord_1213143 prefixEnd_1213143 622925461637452306133363 := by
  unfold tailWord_1213143
  simp only [CollatzResearch.WordTrace]
  refine ⟨44246960243997574174404083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29497973495998382782936055 44246960243997574174404083)
  ·
    refine ⟨66370440365996361261606125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44246960243997574174404083 66370440365996361261606125)
    ·
      refine ⟨24888915137248635473102297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66370440365996361261606125 24888915137248635473102297)
      ·
        refine ⟨18666686352936476604826723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24888915137248635473102297 18666686352936476604826723)
        ·
          refine ⟨28000029529404714907240085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18666686352936476604826723 28000029529404714907240085)
          ·
            refine ⟨1312501384190846011276879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28000029529404714907240085 1312501384190846011276879)
            ·
              refine ⟨1968752076286269016915319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312501384190846011276879 1968752076286269016915319)
              ·
                refine ⟨2953128114429403525372979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968752076286269016915319 2953128114429403525372979)
                ·
                  refine ⟨4429692171644105288059469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953128114429403525372979 4429692171644105288059469)
                  ·
                    refine ⟨1661134564366539483022301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4429692171644105288059469 1661134564366539483022301)
                    ·
                      refine ⟨622925461637452306133363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1661134564366539483022301 622925461637452306133363)
                      ·
                        rfl

theorem cell23_1213143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_1213143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213143 prefixEnd_1213143 := by exact prefixLift 1213143
  have htrace : WordTrace (prefixWord ++ tailWord_1213143) baseStart_1213143 baseEnd_1213143 := by
    simpa [prefixWord, tailWord_1213143, baseEnd_1213143] using wordTrace_append hprefix tailTrace_1213143
  have hstable : (prefixWord ++ tailWord_1213143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213143).length < 2 ^ (prefixWord ++ tailWord_1213143).sum := by decide
  have hdescent : baseEnd_1213143 < baseStart_1213143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213170 : List Nat := [3, 2, 1, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_1213170 : Nat := 118140960795 + 1213170 * 2 ^ 59
def prefixEnd_1213170 : Nat := 4983230072969 + 3 ^ 40 * 1213170 * 2
def baseEnd_1213170 : Nat := 622939325615123700495739

theorem tailTrace_1213170 : CollatzResearch.WordTrace tailWord_1213170 prefixEnd_1213170 622939325615123700495739 := by
  unfold tailWord_1213170
  simp only [CollatzResearch.WordTrace]
  refine ⟨11061986253724939446409241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29498630009933171857091309 11061986253724939446409241)
  ·
    refine ⟨8296489690293704584806931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11061986253724939446409241 8296489690293704584806931)
    ·
      refine ⟨12444734535440556877210397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8296489690293704584806931 12444734535440556877210397)
      ·
        refine ⟨4666775450790208828953899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12444734535440556877210397 4666775450790208828953899)
        ·
          refine ⟨7000163176185313243430849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4666775450790208828953899 7000163176185313243430849)
          ·
            refine ⟨5250122382138984932573137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7000163176185313243430849 5250122382138984932573137)
            ·
              refine ⟨3937591786604238699429853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5250122382138984932573137 3937591786604238699429853)
              ·
                refine ⟨1476596919976589512286195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3937591786604238699429853 1476596919976589512286195)
                ·
                  refine ⟨2214895379964884268429293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1476596919976589512286195 2214895379964884268429293)
                  ·
                    refine ⟨830585767486831600660985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2214895379964884268429293 830585767486831600660985)
                    ·
                      refine ⟨622939325615123700495739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830585767486831600660985 622939325615123700495739)
                      ·
                        rfl

theorem cell23_1213170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_1213170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213170 prefixEnd_1213170 := by exact prefixLift 1213170
  have htrace : WordTrace (prefixWord ++ tailWord_1213170) baseStart_1213170 baseEnd_1213170 := by
    simpa [prefixWord, tailWord_1213170, baseEnd_1213170] using wordTrace_append hprefix tailTrace_1213170
  have hstable : (prefixWord ++ tailWord_1213170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213170).length < 2 ^ (prefixWord ++ tailWord_1213170).sum := by decide
  have hdescent : baseEnd_1213170 < baseStart_1213170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213256 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_1213256 : Nat := 118140960795 + 1213256 * 2 ^ 59
def prefixEnd_1213256 : Nat := 4983230072969 + 3 ^ 40 * 1213256 * 2
def baseEnd_1213256 : Nat := 622983484951410364020343

theorem tailTrace_1213256 : CollatzResearch.WordTrace tailWord_1213256 prefixEnd_1213256 622983484951410364020343 := by
  unfold tailWord_1213256
  simp only [CollatzResearch.WordTrace]
  refine ⟨22125540846294097236633811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29500721128392129648845081 22125540846294097236633811)
  ·
    refine ⟨33188311269441145854950717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22125540846294097236633811 33188311269441145854950717)
    ·
      refine ⟨12445616726040429695606519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33188311269441145854950717 12445616726040429695606519)
      ·
        refine ⟨18668425089060644543409779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12445616726040429695606519 18668425089060644543409779)
        ·
          refine ⟨28002637633590966815114669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18668425089060644543409779 28002637633590966815114669)
          ·
            refine ⟨10500989112596612555668001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28002637633590966815114669 10500989112596612555668001)
            ·
              refine ⟨7875741834447459416751001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10500989112596612555668001 7875741834447459416751001)
              ·
                refine ⟨5906806375835594562563251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7875741834447459416751001 5906806375835594562563251)
                ·
                  refine ⟨8860209563753391843844877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5906806375835594562563251 8860209563753391843844877)
                  ·
                    refine ⟨3322578586407521941441829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8860209563753391843844877 3322578586407521941441829)
                    ·
                      refine ⟨622983484951410364020343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3322578586407521941441829 622983484951410364020343)
                      ·
                        rfl

theorem cell23_1213256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_1213256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213256 prefixEnd_1213256 := by exact prefixLift 1213256
  have htrace : WordTrace (prefixWord ++ tailWord_1213256) baseStart_1213256 baseEnd_1213256 := by
    simpa [prefixWord, tailWord_1213256, baseEnd_1213256] using wordTrace_append hprefix tailTrace_1213256
  have hstable : (prefixWord ++ tailWord_1213256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213256).length < 2 ^ (prefixWord ++ tailWord_1213256).sum := by decide
  have hdescent : baseEnd_1213256 < baseStart_1213256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213273 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 4]
def baseStart_1213273 : Nat := 118140960795 + 1213273 * 2 ^ 59
def prefixEnd_1213273 : Nat := 4983230072969 + 3 ^ 40 * 1213273 * 2
def baseEnd_1213273 : Nat := 622992214122536797507765

theorem tailTrace_1213273 : CollatzResearch.WordTrace tailWord_1213273 prefixEnd_1213273 622992214122536797507765 := by
  unfold tailWord_1213273
  simp only [CollatzResearch.WordTrace]
  refine ⟨44251701733526606376636473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29501134489017737584424315 44251701733526606376636473)
  ·
    refine ⟨33188776300144954782477355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44251701733526606376636473 33188776300144954782477355)
    ·
      refine ⟨49783164450217432173716033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33188776300144954782477355 49783164450217432173716033)
      ·
        refine ⟨37337373337663074130287025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49783164450217432173716033 37337373337663074130287025)
        ·
          refine ⟨28003030003247305597715269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37337373337663074130287025 28003030003247305597715269)
          ·
            refine ⟨5250568125608869799571613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28003030003247305597715269 5250568125608869799571613)
            ·
              refine ⟨1968963047103326174839355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5250568125608869799571613 1968963047103326174839355)
              ·
                refine ⟨2953444570654989262259033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968963047103326174839355 2953444570654989262259033)
                ·
                  refine ⟨2215083427991241946694275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2953444570654989262259033 2215083427991241946694275)
                  ·
                    refine ⟨3322625141986862920041413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2215083427991241946694275 3322625141986862920041413)
                    ·
                      refine ⟨622992214122536797507765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3322625141986862920041413 622992214122536797507765)
                      ·
                        rfl

theorem cell23_1213273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_1213273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213273 prefixEnd_1213273 := by exact prefixLift 1213273
  have htrace : WordTrace (prefixWord ++ tailWord_1213273) baseStart_1213273 baseEnd_1213273 := by
    simpa [prefixWord, tailWord_1213273, baseEnd_1213273] using wordTrace_append hprefix tailTrace_1213273
  have hstable : (prefixWord ++ tailWord_1213273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213273).length < 2 ^ (prefixWord ++ tailWord_1213273).sum := by decide
  have hdescent : baseEnd_1213273 < baseStart_1213273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213293 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1213293 : Nat := 118140960795 + 1213293 * 2 ^ 59
def prefixEnd_1213293 : Nat := 4983230072969 + 3 ^ 40 * 1213293 * 2
def baseEnd_1213293 : Nat := 623002483735626719257673

theorem tailTrace_1213293 : CollatzResearch.WordTrace tailWord_1213293 prefixEnd_1213293 623002483735626719257673 := by
  unfold tailWord_1213293
  simp only [CollatzResearch.WordTrace]
  refine ⟨44252431193454149792364533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29501620795636099861576355 44252431193454149792364533)
  ·
    refine ⟨4148665424386326543034175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44252431193454149792364533 4148665424386326543034175)
    ·
      refine ⟨6222998136579489814551263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4148665424386326543034175 6222998136579489814551263)
      ·
        refine ⟨9334497204869234721826895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6222998136579489814551263 9334497204869234721826895)
        ·
          refine ⟨14001745807303852082740343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9334497204869234721826895 14001745807303852082740343)
          ·
            refine ⟨21002618710955778124110515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14001745807303852082740343 21002618710955778124110515)
            ·
              refine ⟨31503928066433667186165773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21002618710955778124110515 31503928066433667186165773)
              ·
                refine ⟨11813973024912625194812165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31503928066433667186165773 11813973024912625194812165)
                ·
                  refine ⟨2215119942171117224027281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11813973024912625194812165 2215119942171117224027281)
                  ·
                    refine ⟨1661339956628337918020461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2215119942171117224027281 1661339956628337918020461)
                    ·
                      refine ⟨623002483735626719257673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1661339956628337918020461 623002483735626719257673)
                      ·
                        rfl

theorem cell23_1213293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1213293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213293 prefixEnd_1213293 := by exact prefixLift 1213293
  have htrace : WordTrace (prefixWord ++ tailWord_1213293) baseStart_1213293 baseEnd_1213293 := by
    simpa [prefixWord, tailWord_1213293, baseEnd_1213293] using wordTrace_append hprefix tailTrace_1213293
  have hstable : (prefixWord ++ tailWord_1213293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213293).length < 2 ^ (prefixWord ++ tailWord_1213293).sum := by decide
  have hdescent : baseEnd_1213293 < baseStart_1213293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213316 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1213316 : Nat := 118140960795 + 1213316 * 2 ^ 59
def prefixEnd_1213316 : Nat := 4983230072969 + 3 ^ 40 * 1213316 * 2
def baseEnd_1213316 : Nat := 623014293790680129270067

theorem tailTrace_1213316 : CollatzResearch.WordTrace tailWord_1213316 prefixEnd_1213316 623014293790680129270067 := by
  unfold tailWord_1213316
  simp only [CollatzResearch.WordTrace]
  refine ⟨22126635036185412360225901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29502180048247216480301201 22126635036185412360225901)
  ·
    refine ⟨8297488138569529635084713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22126635036185412360225901 8297488138569529635084713)
    ·
      refine ⟨6223116103927147226313535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8297488138569529635084713 6223116103927147226313535)
      ·
        refine ⟨9334674155890720839470303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6223116103927147226313535 9334674155890720839470303)
        ·
          refine ⟨14002011233836081259205455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9334674155890720839470303 14002011233836081259205455)
          ·
            refine ⟨21003016850754121888808183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14002011233836081259205455 21003016850754121888808183)
            ·
              refine ⟨31504525276131182833212275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21003016850754121888808183 31504525276131182833212275)
              ·
                refine ⟨47256787914196774249818413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31504525276131182833212275 47256787914196774249818413)
                ·
                  refine ⟨17721295467823790343681905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47256787914196774249818413 17721295467823790343681905)
                  ·
                    refine ⟨13290971600867842757761429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17721295467823790343681905 13290971600867842757761429)
                    ·
                      refine ⟨623014293790680129270067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13290971600867842757761429 623014293790680129270067)
                      ·
                        rfl

theorem cell23_1213316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1213316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213316 prefixEnd_1213316 := by exact prefixLift 1213316
  have htrace : WordTrace (prefixWord ++ tailWord_1213316) baseStart_1213316 baseEnd_1213316 := by
    simpa [prefixWord, tailWord_1213316, baseEnd_1213316] using wordTrace_append hprefix tailTrace_1213316
  have hstable : (prefixWord ++ tailWord_1213316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213316).length < 2 ^ (prefixWord ++ tailWord_1213316).sum := by decide
  have hdescent : baseEnd_1213316 < baseStart_1213316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213356 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_1213356 : Nat := 118140960795 + 1213356 * 2 ^ 59
def prefixEnd_1213356 : Nat := 4983230072969 + 3 ^ 40 * 1213356 * 2
def baseEnd_1213356 : Nat := 207678277672286657589961

theorem tailTrace_1213356 : CollatzResearch.WordTrace tailWord_1213356 prefixEnd_1213356 207678277672286657589961 := by
  unfold tailWord_1213356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22127364496112955775953961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29503152661483941034605281 22127364496112955775953961)
  ·
    refine ⟨16595523372084716831965471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22127364496112955775953961 16595523372084716831965471)
    ·
      refine ⟨24893285058127075247948207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16595523372084716831965471 24893285058127075247948207)
      ·
        refine ⟨37339927587190612871922311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24893285058127075247948207 37339927587190612871922311)
        ·
          refine ⟨56009891380785919307883467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37339927587190612871922311 56009891380785919307883467)
          ·
            refine ⟨84014837071178878961825201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56009891380785919307883467 84014837071178878961825201)
            ·
              refine ⟨63011127803384159221368901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84014837071178878961825201 63011127803384159221368901)
              ·
                refine ⟨11814586463134529854006669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63011127803384159221368901 11814586463134529854006669)
                ·
                  refine ⟨4430469923675448695252501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11814586463134529854006669 4430469923675448695252501)
                  ·
                    refine ⟨207678277672286657589961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4430469923675448695252501 207678277672286657589961)
                    ·
                      rfl

theorem cell23_1213356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_1213356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213356 prefixEnd_1213356 := by exact prefixLift 1213356
  have htrace : WordTrace (prefixWord ++ tailWord_1213356) baseStart_1213356 baseEnd_1213356 := by
    simpa [prefixWord, tailWord_1213356, baseEnd_1213356] using wordTrace_append hprefix tailTrace_1213356
  have hstable : (prefixWord ++ tailWord_1213356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213356).length < 2 ^ (prefixWord ++ tailWord_1213356).sum := by decide
  have hdescent : baseEnd_1213356 < baseStart_1213356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213363 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 2, 6, 2]
def baseStart_1213363 : Nat := 118140960795 + 1213363 * 2 ^ 59
def prefixEnd_1213363 : Nat := 4983230072969 + 3 ^ 40 * 1213363 * 2
def baseEnd_1213363 : Nat := 623038427381441445382351

theorem tailTrace_1213363 : CollatzResearch.WordTrace tailWord_1213363 prefixEnd_1213363 623038427381441445382351 := by
  unfold tailWord_1213363
  simp only [CollatzResearch.WordTrace]
  refine ⟨44254984303200551747412743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29503322868800367831608495 44254984303200551747412743)
  ·
    refine ⟨66382476454800827621119115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44254984303200551747412743 66382476454800827621119115)
    ·
      refine ⟨99573714682201241431678673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66382476454800827621119115 99573714682201241431678673)
      ·
        refine ⟨74680286011650931073759005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99573714682201241431678673 74680286011650931073759005)
        ·
          refine ⟨28005107254369099152659627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74680286011650931073759005 28005107254369099152659627)
          ·
            refine ⟨42007660881553648728989441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28005107254369099152659627 42007660881553648728989441)
            ·
              refine ⟨31505745661165236546742081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42007660881553648728989441 31505745661165236546742081)
              ·
                refine ⟨23629309245873927410056561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31505745661165236546742081 23629309245873927410056561)
                ·
                  refine ⟨17721981934405445557542421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23629309245873927410056561 17721981934405445557542421)
                  ·
                    refine ⟨830717903175255260509801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17721981934405445557542421 830717903175255260509801)
                    ·
                      refine ⟨623038427381441445382351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830717903175255260509801 623038427381441445382351)
                      ·
                        rfl

theorem cell23_1213363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 6, 2].length) (baseStart_1213363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213363 prefixEnd_1213363 := by exact prefixLift 1213363
  have htrace : WordTrace (prefixWord ++ tailWord_1213363) baseStart_1213363 baseEnd_1213363 := by
    simpa [prefixWord, tailWord_1213363, baseEnd_1213363] using wordTrace_append hprefix tailTrace_1213363
  have hstable : (prefixWord ++ tailWord_1213363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213363).length < 2 ^ (prefixWord ++ tailWord_1213363).sum := by decide
  have hdescent : baseEnd_1213363 < baseStart_1213363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213364 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 6]
def baseStart_1213364 : Nat := 118140960795 + 1213364 * 2 ^ 59
def prefixEnd_1213364 : Nat := 4983230072969 + 3 ^ 40 * 1213364 * 2
def baseEnd_1213364 : Nat := 69226548984677326829983

theorem tailTrace_1213364 : CollatzResearch.WordTrace tailWord_1213364 prefixEnd_1213364 69226548984677326829983 := by
  unfold tailWord_1213364
  simp only [CollatzResearch.WordTrace]
  refine ⟨22127510388098464459099573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29503347184131285945466097 22127510388098464459099573)
  ·
    refine ⟨2074454098884231043040585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22127510388098464459099573 2074454098884231043040585)
    ·
      refine ⟨1555840574163173282280439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2074454098884231043040585 1555840574163173282280439)
      ·
        refine ⟨2333760861244759923420659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555840574163173282280439 2333760861244759923420659)
        ·
          refine ⟨3500641291867139885130989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2333760861244759923420659 3500641291867139885130989)
          ·
            refine ⟨1312740484450177456924121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3500641291867139885130989 1312740484450177456924121)
            ·
              refine ⟨984555363337633092693091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312740484450177456924121 984555363337633092693091)
              ·
                refine ⟨1476833045006449639039637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984555363337633092693091 1476833045006449639039637)
                ·
                  refine ⟨69226548984677326829983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1476833045006449639039637 69226548984677326829983)
                  ·
                    rfl

theorem cell23_1213364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_1213364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213364 prefixEnd_1213364 := by exact prefixLift 1213364
  have htrace : WordTrace (prefixWord ++ tailWord_1213364) baseStart_1213364 baseEnd_1213364 := by
    simpa [prefixWord, tailWord_1213364, baseEnd_1213364] using wordTrace_append hprefix tailTrace_1213364
  have hstable : (prefixWord ++ tailWord_1213364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213364).length < 2 ^ (prefixWord ++ tailWord_1213364).sum := by decide
  have hdescent : baseEnd_1213364 < baseStart_1213364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213393 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_1213393 : Nat := 118140960795 + 1213393 * 2 ^ 59
def prefixEnd_1213393 : Nat := 4983230072969 + 3 ^ 40 * 1213393 * 2
def baseEnd_1213393 : Nat := 623053831801076328007213

theorem tailTrace_1213393 : CollatzResearch.WordTrace tailWord_1213393 prefixEnd_1213393 623053831801076328007213 := by
  unfold tailWord_1213393
  simp only [CollatzResearch.WordTrace]
  refine ⟨44256078493091866871004833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29504052328727911247336555 44256078493091866871004833)
  ·
    refine ⟨33192058869818900153253625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44256078493091866871004833 33192058869818900153253625)
    ·
      refine ⟨24894044152364175114940219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33192058869818900153253625 24894044152364175114940219)
      ·
        refine ⟨37341066228546262672410329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24894044152364175114940219 37341066228546262672410329)
        ·
          refine ⟨28005799671409697004307747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37341066228546262672410329 28005799671409697004307747)
          ·
            refine ⟨42008699507114545506461621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28005799671409697004307747 42008699507114545506461621)
            ·
              refine ⟨3938315578791988641230777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42008699507114545506461621 3938315578791988641230777)
              ·
                refine ⟨2953736684093991480923083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3938315578791988641230777 2953736684093991480923083)
                ·
                  refine ⟨4430605026140987221384625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953736684093991480923083 4430605026140987221384625)
                  ·
                    refine ⟨3322953769605740416038469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4430605026140987221384625 3322953769605740416038469)
                    ·
                      refine ⟨623053831801076328007213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3322953769605740416038469 623053831801076328007213)
                      ·
                        rfl

theorem cell23_1213393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_1213393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213393 prefixEnd_1213393 := by exact prefixLift 1213393
  have htrace : WordTrace (prefixWord ++ tailWord_1213393) baseStart_1213393 baseEnd_1213393 := by
    simpa [prefixWord, tailWord_1213393, baseEnd_1213393] using wordTrace_append hprefix tailTrace_1213393
  have hstable : (prefixWord ++ tailWord_1213393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213393).length < 2 ^ (prefixWord ++ tailWord_1213393).sum := by decide
  have hdescent : baseEnd_1213393 < baseStart_1213393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213400 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 1, 1, 5]
def baseStart_1213400 : Nat := 118140960795 + 1213400 * 2 ^ 59
def prefixEnd_1213400 : Nat := 4983230072969 + 3 ^ 40 * 1213400 * 2
def baseEnd_1213400 : Nat := 623057426165657800619681

theorem tailTrace_1213400 : CollatzResearch.WordTrace tailWord_1213400 prefixEnd_1213400 623057426165657800619681 := by
  unfold tailWord_1213400
  simp only [CollatzResearch.WordTrace]
  refine ⟨22128166902033253533254827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29504222536044338044339769 22128166902033253533254827)
  ·
    refine ⟨33192250353049880299882241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22128166902033253533254827 33192250353049880299882241)
    ·
      refine ⟨24894187764787410224911681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33192250353049880299882241 24894187764787410224911681)
      ·
        refine ⟨18670640823590557668683761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24894187764787410224911681 18670640823590557668683761)
        ·
          refine ⟨14002980617692918251512821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18670640823590557668683761 14002980617692918251512821)
          ·
            refine ⟨1312779432908711086079327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14002980617692918251512821 1312779432908711086079327)
            ·
              refine ⟨1969169149363066629118991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312779432908711086079327 1969169149363066629118991)
              ·
                refine ⟨2953753724044599943678487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969169149363066629118991 2953753724044599943678487)
                ·
                  refine ⟨4430630586066899915517731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2953753724044599943678487 4430630586066899915517731)
                  ·
                    refine ⟨6645945879100349873276597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4430630586066899915517731 6645945879100349873276597)
                    ·
                      refine ⟨623057426165657800619681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6645945879100349873276597 623057426165657800619681)
                      ·
                        rfl

theorem cell23_1213400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_1213400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213400 prefixEnd_1213400 := by exact prefixLift 1213400
  have htrace : WordTrace (prefixWord ++ tailWord_1213400) baseStart_1213400 baseEnd_1213400 := by
    simpa [prefixWord, tailWord_1213400, baseEnd_1213400] using wordTrace_append hprefix tailTrace_1213400
  have hstable : (prefixWord ++ tailWord_1213400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213400).length < 2 ^ (prefixWord ++ tailWord_1213400).sum := by decide
  have hdescent : baseEnd_1213400 < baseStart_1213400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213407 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 2, 4]
def baseStart_1213407 : Nat := 118140960795 + 1213407 * 2 ^ 59
def prefixEnd_1213407 : Nat := 4983230072969 + 3 ^ 40 * 1213407 * 2
def baseEnd_1213407 : Nat := 207687006843413091077383

theorem tailTrace_1213407 : CollatzResearch.WordTrace tailWord_1213407 prefixEnd_1213407 207687006843413091077383 := by
  unfold tailWord_1213407
  simp only [CollatzResearch.WordTrace]
  refine ⟨44256589115041147262014475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29504392743360764841342983 44256589115041147262014475)
  ·
    refine ⟨66384883672561720893021713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44256589115041147262014475 66384883672561720893021713)
    ·
      refine ⟨49788662754421290669766285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66384883672561720893021713 49788662754421290669766285)
      ·
        refine ⟨18670748532907984001162357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49788662754421290669766285 18670748532907984001162357)
        ·
          refine ⟨1750382674960123500108971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18670748532907984001162357 1750382674960123500108971)
          ·
            refine ⟨2625574012440185250163457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750382674960123500108971 2625574012440185250163457)
            ·
              refine ⟨1969180509330138937622593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2625574012440185250163457 1969180509330138937622593)
              ·
                refine ⟨1476885381997604203216945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1969180509330138937622593 1476885381997604203216945)
                ·
                  refine ⟨1107664036498203152412709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1476885381997604203216945 1107664036498203152412709)
                  ·
                    refine ⟨207687006843413091077383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1107664036498203152412709 207687006843413091077383)
                    ·
                      rfl

theorem cell23_1213407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 4].length) (baseStart_1213407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213407 prefixEnd_1213407 := by exact prefixLift 1213407
  have htrace : WordTrace (prefixWord ++ tailWord_1213407) baseStart_1213407 baseEnd_1213407 := by
    simpa [prefixWord, tailWord_1213407, baseEnd_1213407] using wordTrace_append hprefix tailTrace_1213407
  have hstable : (prefixWord ++ tailWord_1213407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213407).length < 2 ^ (prefixWord ++ tailWord_1213407).sum := by decide
  have hdescent : baseEnd_1213407 < baseStart_1213407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213458 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_1213458 : Nat := 118140960795 + 1213458 * 2 ^ 59
def prefixEnd_1213458 : Nat := 4983230072969 + 3 ^ 40 * 1213458 * 2
def baseEnd_1213458 : Nat := 207695736014539524564805

theorem tailTrace_1213458 : CollatzResearch.WordTrace tailWord_1213458 prefixEnd_1213458 207695736014539524564805 := by
  unfold tailWord_1213458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11064612309464095743030257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29505632825237588648080685 11064612309464095743030257)
  ·
    refine ⟨8298459232098071807272693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11064612309464095743030257 8298459232098071807272693)
    ·
      refine ⟨777980553009194231931815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8298459232098071807272693 777980553009194231931815)
      ·
        refine ⟨1166970829513791347897723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 777980553009194231931815 1166970829513791347897723)
        ·
          refine ⟨1750456244270687021846585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1166970829513791347897723 1750456244270687021846585)
          ·
            refine ⟨1312842183203015266384939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1750456244270687021846585 1312842183203015266384939)
            ·
              refine ⟨1969263274804522899577409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312842183203015266384939 1969263274804522899577409)
              ·
                refine ⟨1476947456103392174683057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1969263274804522899577409 1476947456103392174683057)
                ·
                  refine ⟨1107710592077544131012293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1476947456103392174683057 1107710592077544131012293)
                  ·
                    refine ⟨207695736014539524564805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1107710592077544131012293 207695736014539524564805)
                    ·
                      rfl

theorem cell23_1213458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_1213458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213458 prefixEnd_1213458 := by exact prefixLift 1213458
  have htrace : WordTrace (prefixWord ++ tailWord_1213458) baseStart_1213458 baseEnd_1213458 := by
    simpa [prefixWord, tailWord_1213458, baseEnd_1213458] using wordTrace_append hprefix tailTrace_1213458
  have hstable : (prefixWord ++ tailWord_1213458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213458).length < 2 ^ (prefixWord ++ tailWord_1213458).sum := by decide
  have hdescent : baseEnd_1213458 < baseStart_1213458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213464 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 2, 1, 3]
def baseStart_1213464 : Nat := 118140960795 + 1213464 * 2 ^ 59
def prefixEnd_1213464 : Nat := 4983230072969 + 3 ^ 40 * 1213464 * 2
def baseEnd_1213464 : Nat := 623090288927545550219387

theorem tailTrace_1213464 : CollatzResearch.WordTrace tailWord_1213464 prefixEnd_1213464 623090288927545550219387 := by
  unfold tailWord_1213464
  simp only [CollatzResearch.WordTrace]
  refine ⟨22129334037917322998419723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29505778717223097331226297 22129334037917322998419723)
  ·
    refine ⟨33194001056875984497629585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22129334037917322998419723 33194001056875984497629585)
    ·
      refine ⟨24895500792656988373222189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33194001056875984497629585 24895500792656988373222189)
      ·
        refine ⟨9335812797246370639958321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24895500792656988373222189 9335812797246370639958321)
        ·
          refine ⟨7001859597934777979968741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9335812797246370639958321 7001859597934777979968741)
          ·
            refine ⟨1312848674612770871244139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7001859597934777979968741 1312848674612770871244139)
            ·
              refine ⟨1969273011919156306866209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1312848674612770871244139 1969273011919156306866209)
              ·
                refine ⟨1476954758939367230149657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1969273011919156306866209 1476954758939367230149657)
                ·
                  refine ⟨1107716069204525422612243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1476954758939367230149657 1107716069204525422612243)
                  ·
                    refine ⟨1661574103806788133918365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1107716069204525422612243 1661574103806788133918365)
                    ·
                      refine ⟨623090288927545550219387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1661574103806788133918365 623090288927545550219387)
                      ·
                        rfl

theorem cell23_1213464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_1213464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213464 prefixEnd_1213464 := by exact prefixLift 1213464
  have htrace : WordTrace (prefixWord ++ tailWord_1213464) baseStart_1213464 baseEnd_1213464 := by
    simpa [prefixWord, tailWord_1213464, baseEnd_1213464] using wordTrace_append hprefix tailTrace_1213464
  have hstable : (prefixWord ++ tailWord_1213464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213464).length < 2 ^ (prefixWord ++ tailWord_1213464).sum := by decide
  have hdescent : baseEnd_1213464 < baseStart_1213464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213483 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 4]
def baseStart_1213483 : Nat := 118140960795 + 1213483 * 2 ^ 59
def prefixEnd_1213483 : Nat := 4983230072969 + 3 ^ 40 * 1213483 * 2
def baseEnd_1213483 : Nat := 623100045059980975881799

theorem tailTrace_1213483 : CollatzResearch.WordTrace tailWord_1213483 prefixEnd_1213483 623100045059980975881799 := by
  unfold tailWord_1213483
  simp only [CollatzResearch.WordTrace]
  refine ⟨44259361062765812241781103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29506240708510541494520735 44259361062765812241781103)
  ·
    refine ⟨66389041594148718362671655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44259361062765812241781103 66389041594148718362671655)
    ·
      refine ⟨99583562391223077544007483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66389041594148718362671655 99583562391223077544007483)
      ·
        refine ⟨149375343586834616316011225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99583562391223077544007483 149375343586834616316011225)
        ·
          refine ⟨112031507690125962237008419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149375343586834616316011225 112031507690125962237008419)
          ·
            refine ⟨168047261535188943355512629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112031507690125962237008419 168047261535188943355512629)
            ·
              refine ⟨15754430768923963439579309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168047261535188943355512629 15754430768923963439579309)
              ·
                refine ⟨5907911538346486289842241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15754430768923963439579309 5907911538346486289842241)
                ·
                  refine ⟨4430933653759864717381681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5907911538346486289842241 4430933653759864717381681)
                  ·
                    refine ⟨3323200240319898538036261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4430933653759864717381681 3323200240319898538036261)
                    ·
                      refine ⟨623100045059980975881799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3323200240319898538036261 623100045059980975881799)
                      ·
                        rfl

theorem cell23_1213483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 4].length) (baseStart_1213483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213483 prefixEnd_1213483 := by exact prefixLift 1213483
  have htrace : WordTrace (prefixWord ++ tailWord_1213483) baseStart_1213483 baseEnd_1213483 := by
    simpa [prefixWord, tailWord_1213483, baseEnd_1213483] using wordTrace_append hprefix tailTrace_1213483
  have hstable : (prefixWord ++ tailWord_1213483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213483).length < 2 ^ (prefixWord ++ tailWord_1213483).sum := by decide
  have hdescent : baseEnd_1213483 < baseStart_1213483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213523 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 4, 5]
def baseStart_1213523 : Nat := 118140960795 + 1213523 * 2 ^ 59
def prefixEnd_1213523 : Nat := 4983230072969 + 3 ^ 40 * 1213523 * 2
def baseEnd_1213523 : Nat := 207706861428720273127205

theorem tailTrace_1213523 : CollatzResearch.WordTrace tailWord_1213523 prefixEnd_1213523 207706861428720273127205 := by
  unfold tailWord_1213523
  simp only [CollatzResearch.WordTrace]
  refine ⟨44260819982620899073237223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29507213321747266048824815 44260819982620899073237223)
  ·
    refine ⟨66391229973931348609855835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44260819982620899073237223 66391229973931348609855835)
    ·
      refine ⟨99586844960897022914783753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66391229973931348609855835 99586844960897022914783753)
      ·
        refine ⟨74690133720672767186087815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99586844960897022914783753 74690133720672767186087815)
        ·
          refine ⟨112035200581009150779131723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74690133720672767186087815 112035200581009150779131723)
          ·
            refine ⟨168052800871513726168697585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112035200581009150779131723 168052800871513726168697585)
            ·
              refine ⟨126039600653635294626523189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168052800871513726168697585 126039600653635294626523189)
              ·
                refine ⟨11816212561278308871236549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126039600653635294626523189 11816212561278308871236549)
                ·
                  refine ⟨2215539855239682913356853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11816212561278308871236549 2215539855239682913356853)
                  ·
                    refine ⟨207706861428720273127205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2215539855239682913356853 207706861428720273127205)
                    ·
                      rfl

theorem cell23_1213523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 5].length) (baseStart_1213523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213523 prefixEnd_1213523 := by exact prefixLift 1213523
  have htrace : WordTrace (prefixWord ++ tailWord_1213523) baseStart_1213523 baseEnd_1213523 := by
    simpa [prefixWord, tailWord_1213523, baseEnd_1213523] using wordTrace_append hprefix tailTrace_1213523
  have hstable : (prefixWord ++ tailWord_1213523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213523).length < 2 ^ (prefixWord ++ tailWord_1213523).sum := by decide
  have hdescent : baseEnd_1213523 < baseStart_1213523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213538 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1213538 : Nat := 118140960795 + 1213538 * 2 ^ 59
def prefixEnd_1213538 : Nat := 4983230072969 + 3 ^ 40 * 1213538 * 2
def baseEnd_1213538 : Nat := 623128286495978260694047

theorem tailTrace_1213538 : CollatzResearch.WordTrace tailWord_1213538 prefixEnd_1213538 623128286495978260694047 := by
  unfold tailWord_1213538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11065341769391639158758317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29507578051711037756688845 11065341769391639158758317)
  ·
    refine ⟨4149503163521864684534369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11065341769391639158758317 4149503163521864684534369)
    ·
      refine ⟨3112127372641398513400777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4149503163521864684534369 3112127372641398513400777)
      ·
        refine ⟨2334095529481048885050583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3112127372641398513400777 2334095529481048885050583)
        ·
          refine ⟨3501143294221573327575875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334095529481048885050583 3501143294221573327575875)
          ·
            refine ⟨5251714941332359991363813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501143294221573327575875 5251714941332359991363813)
            ·
              refine ⟨984696551499817498380715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5251714941332359991363813 984696551499817498380715)
              ·
                refine ⟨1477044827249726247571073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984696551499817498380715 1477044827249726247571073)
                ·
                  refine ⟨1107783620437294685678305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1477044827249726247571073 1107783620437294685678305)
                  ·
                    refine ⟨830837715327971014258729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1107783620437294685678305 830837715327971014258729)
                    ·
                      refine ⟨623128286495978260694047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830837715327971014258729 623128286495978260694047)
                      ·
                        rfl

theorem cell23_1213538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1213538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213538 prefixEnd_1213538 := by exact prefixLift 1213538
  have htrace : WordTrace (prefixWord ++ tailWord_1213538) baseStart_1213538 baseEnd_1213538 := by
    simpa [prefixWord, tailWord_1213538, baseEnd_1213538] using wordTrace_append hprefix tailTrace_1213538
  have hstable : (prefixWord ++ tailWord_1213538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213538).length < 2 ^ (prefixWord ++ tailWord_1213538).sum := by decide
  have hdescent : baseEnd_1213538 < baseStart_1213538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213560 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_1213560 : Nat := 118140960795 + 1213560 * 2 ^ 59
def prefixEnd_1213560 : Nat := 4983230072969 + 3 ^ 40 * 1213560 * 2
def baseEnd_1213560 : Nat := 623139583070377174618945

theorem tailTrace_1213560 : CollatzResearch.WordTrace tailWord_1213560 prefixEnd_1213560 623139583070377174618945 := by
  unfold tailWord_1213560
  simp only [CollatzResearch.WordTrace]
  refine ⟨22131084741743427196167067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29508112988991236261556089 22131084741743427196167067)
  ·
    refine ⟨33196627112615140794250601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22131084741743427196167067 33196627112615140794250601)
    ·
      refine ⟨24897470334461355595687951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33196627112615140794250601 24897470334461355595687951)
      ·
        refine ⟨37346205501692033393531927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24897470334461355595687951 37346205501692033393531927)
        ·
          refine ⟨56019308252538050090297891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37346205501692033393531927 56019308252538050090297891)
          ·
            refine ⟨84028962378807075135446837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56019308252538050090297891 84028962378807075135446837)
            ·
              refine ⟨7877715223013163293948141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84028962378807075135446837 7877715223013163293948141)
              ·
                refine ⟨2954143208629936235230553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7877715223013163293948141 2954143208629936235230553)
                ·
                  refine ⟨2215607406472452176422915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2954143208629936235230553 2215607406472452176422915)
                  ·
                    refine ⟨3323411109708678264634373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2215607406472452176422915 3323411109708678264634373)
                    ·
                      refine ⟨623139583070377174618945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3323411109708678264634373 623139583070377174618945)
                      ·
                        rfl

theorem cell23_1213560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_1213560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213560 prefixEnd_1213560 := by exact prefixLift 1213560
  have htrace : WordTrace (prefixWord ++ tailWord_1213560) baseStart_1213560 baseEnd_1213560 := by
    simpa [prefixWord, tailWord_1213560, baseEnd_1213560] using wordTrace_append hprefix tailTrace_1213560
  have hstable : (prefixWord ++ tailWord_1213560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213560).length < 2 ^ (prefixWord ++ tailWord_1213560).sum := by decide
  have hdescent : baseEnd_1213560 < baseStart_1213560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213594 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2]
def baseStart_1213594 : Nat := 118140960795 + 1213594 * 2 ^ 59
def prefixEnd_1213594 : Nat := 4983230072969 + 3 ^ 40 * 1213594 * 2
def baseEnd_1213594 : Nat := 623157041412630041593789

theorem tailTrace_1213594 : CollatzResearch.WordTrace tailWord_1213594 prefixEnd_1213594 623157041412630041593789 := by
  unfold tailWord_1213594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11065852391340919549767959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29508939710242452132714557 11065852391340919549767959)
  ·
    refine ⟨16598778587011379324651939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11065852391340919549767959 16598778587011379324651939)
    ·
      refine ⟨24898167880517068986977909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16598778587011379324651939 24898167880517068986977909)
      ·
        refine ⟨2334203238798475217529179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24898167880517068986977909 2334203238798475217529179)
        ·
          refine ⟨3501304858197712826293769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334203238798475217529179 3501304858197712826293769)
          ·
            refine ⟨2625978643648284619720327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3501304858197712826293769 2625978643648284619720327)
            ·
              refine ⟨3938967965472426929580491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2625978643648284619720327 3938967965472426929580491)
              ·
                refine ⟨5908451948208640394370737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3938967965472426929580491 5908451948208640394370737)
                ·
                  refine ⟨4431338961156480295778053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5908451948208640394370737 4431338961156480295778053)
                  ·
                    refine ⟨830876055216840055458385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4431338961156480295778053 830876055216840055458385)
                    ·
                      refine ⟨623157041412630041593789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830876055216840055458385 623157041412630041593789)
                      ·
                        rfl

theorem cell23_1213594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_1213594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213594 prefixEnd_1213594 := by exact prefixLift 1213594
  have htrace : WordTrace (prefixWord ++ tailWord_1213594) baseStart_1213594 baseEnd_1213594 := by
    simpa [prefixWord, tailWord_1213594, baseEnd_1213594] using wordTrace_append hprefix tailTrace_1213594
  have hstable : (prefixWord ++ tailWord_1213594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213594).length < 2 ^ (prefixWord ++ tailWord_1213594).sum := by decide
  have hdescent : baseEnd_1213594 < baseStart_1213594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213600 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 6]
def baseStart_1213600 : Nat := 118140960795 + 1213600 * 2 ^ 59
def prefixEnd_1213600 : Nat := 4983230072969 + 3 ^ 40 * 1213600 * 2
def baseEnd_1213600 : Nat := 69240013588506335346529

theorem tailTrace_1213600 : CollatzResearch.WordTrace tailWord_1213600 prefixEnd_1213600 69240013588506335346529 := by
  unfold tailWord_1213600
  simp only [CollatzResearch.WordTrace]
  refine ⟨22131814201670970611895127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29509085602227960815860169 22131814201670970611895127)
  ·
    refine ⟨33197721302506455917842691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22131814201670970611895127 33197721302506455917842691)
    ·
      refine ⟨49796581953759683876764037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33197721302506455917842691 49796581953759683876764037)
      ·
        refine ⟨9336859116329940726893257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49796581953759683876764037 9336859116329940726893257)
        ·
          refine ⟨7002644337247455545169943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9336859116329940726893257 7002644337247455545169943)
          ·
            refine ⟨10503966505871183317754915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7002644337247455545169943 10503966505871183317754915)
            ·
              refine ⟨15755949758806774976632373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10503966505871183317754915 15755949758806774976632373)
              ·
                refine ⟨1477120289888135154059285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15755949758806774976632373 1477120289888135154059285)
                ·
                  refine ⟨69240013588506335346529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1477120289888135154059285 69240013588506335346529)
                  ·
                    rfl

theorem cell23_1213600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 6].length) (baseStart_1213600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213600 prefixEnd_1213600 := by exact prefixLift 1213600
  have htrace : WordTrace (prefixWord ++ tailWord_1213600) baseStart_1213600 baseEnd_1213600 := by
    simpa [prefixWord, tailWord_1213600, baseEnd_1213600] using wordTrace_append hprefix tailTrace_1213600
  have hstable : (prefixWord ++ tailWord_1213600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213600).length < 2 ^ (prefixWord ++ tailWord_1213600).sum := by decide
  have hdescent : baseEnd_1213600 < baseStart_1213600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213637 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 4, 3, 2]
def baseStart_1213637 : Nat := 118140960795 + 1213637 * 2 ^ 59
def prefixEnd_1213637 : Nat := 4983230072969 + 3 ^ 40 * 1213637 * 2
def baseEnd_1213637 : Nat := 623179121080773373356091

theorem tailTrace_1213637 : CollatzResearch.WordTrace tailWord_1213637 prefixEnd_1213637 623179121080773373356091 := by
  unfold tailWord_1213637
  simp only [CollatzResearch.WordTrace]
  refine ⟨44264977904207896542887165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29509985269471931028591443 44264977904207896542887165)
  ·
    refine ⟨16599366714077961203582687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44264977904207896542887165 16599366714077961203582687)
    ·
      refine ⟨24899050071116941805374031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16599366714077961203582687 24899050071116941805374031)
      ·
        refine ⟨37348575106675412708061047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24899050071116941805374031 37348575106675412708061047)
        ·
          refine ⟨56022862660013119062091571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37348575106675412708061047 56022862660013119062091571)
          ·
            refine ⟨84034293990019678593137357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56022862660013119062091571 84034293990019678593137357)
            ·
              refine ⟨31512860246257379472426509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84034293990019678593137357 31512860246257379472426509)
              ·
                refine ⟨11817322592346517302159941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31512860246257379472426509 11817322592346517302159941)
                ·
                  refine ⟨2215747986064971994154989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11817322592346517302159941 2215747986064971994154989)
                  ·
                    refine ⟨830905494774364497808121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215747986064971994154989 830905494774364497808121)
                    ·
                      refine ⟨623179121080773373356091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830905494774364497808121 623179121080773373356091)
                      ·
                        rfl

theorem cell23_1213637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_1213637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213637 prefixEnd_1213637 := by exact prefixLift 1213637
  have htrace : WordTrace (prefixWord ++ tailWord_1213637) baseStart_1213637 baseEnd_1213637 := by
    simpa [prefixWord, tailWord_1213637, baseEnd_1213637] using wordTrace_append hprefix tailTrace_1213637
  have hstable : (prefixWord ++ tailWord_1213637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213637).length < 2 ^ (prefixWord ++ tailWord_1213637).sum := by decide
  have hdescent : baseEnd_1213637 < baseStart_1213637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213694 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1213694 : Nat := 118140960795 + 1213694 * 2 ^ 59
def prefixEnd_1213694 : Nat := 4983230072969 + 3 ^ 40 * 1213694 * 2
def baseEnd_1213694 : Nat := 207736129826026550114443

theorem tailTrace_1213694 : CollatzResearch.WordTrace tailWord_1213694 prefixEnd_1213694 207736129826026550114443 := by
  unfold tailWord_1213694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5533382108125174409714017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29511371243334263518474757 5533382108125174409714017)
  ·
    refine ⟨4150036581093880807285513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5533382108125174409714017 4150036581093880807285513)
    ·
      refine ⟨3112527435820410605464135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4150036581093880807285513 3112527435820410605464135)
      ·
        refine ⟨4668791153730615908196203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3112527435820410605464135 4668791153730615908196203)
        ·
          refine ⟨7003186730595923862294305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4668791153730615908196203 7003186730595923862294305)
          ·
            refine ⟨5252390047946942896720729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7003186730595923862294305 5252390047946942896720729)
            ·
              refine ⟨3939292535960207172540547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5252390047946942896720729 3939292535960207172540547)
              ·
                refine ⟨5908938803940310758810821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939292535960207172540547 5908938803940310758810821)
                ·
                  refine ⟨1107926025738808267277029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5908938803940310758810821 1107926025738808267277029)
                  ·
                    refine ⟨207736129826026550114443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1107926025738808267277029 207736129826026550114443)
                    ·
                      rfl

theorem cell23_1213694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1213694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213694 prefixEnd_1213694 := by exact prefixLift 1213694
  have htrace : WordTrace (prefixWord ++ tailWord_1213694) baseStart_1213694 baseEnd_1213694 := by
    simpa [prefixWord, tailWord_1213694, baseEnd_1213694] using wordTrace_append hprefix tailTrace_1213694
  have hstable : (prefixWord ++ tailWord_1213694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213694).length < 2 ^ (prefixWord ++ tailWord_1213694).sum := by decide
  have hdescent : baseEnd_1213694 < baseStart_1213694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213717 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_1213717 : Nat := 118140960795 + 1213717 * 2 ^ 59
def prefixEnd_1213717 : Nat := 4983230072969 + 3 ^ 40 * 1213717 * 2
def baseEnd_1213717 : Nat := 623220199533133060355723

theorem tailTrace_1213717 : CollatzResearch.WordTrace tailWord_1213717 prefixEnd_1213717 623220199533133060355723 := by
  unfold tailWord_1213717
  simp only [CollatzResearch.WordTrace]
  refine ⟨44267895743918070205799405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29511930495945380137199603 44267895743918070205799405)
  ·
    refine ⟨16600460903969276327174777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44267895743918070205799405 16600460903969276327174777)
    ·
      refine ⟨12450345677976957245381083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16600460903969276327174777 12450345677976957245381083)
      ·
        refine ⟨18675518516965435868071625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12450345677976957245381083 18675518516965435868071625)
        ·
          refine ⟨14006638887724076901053719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18675518516965435868071625 14006638887724076901053719)
          ·
            refine ⟨21009958331586115351580579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14006638887724076901053719 21009958331586115351580579)
            ·
              refine ⟨31514937497379173027370869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21009958331586115351580579 31514937497379173027370869)
              ·
                refine ⟨2954525390379297471316019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31514937497379173027370869 2954525390379297471316019)
                ·
                  refine ⟨4431788085568946206974029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954525390379297471316019 4431788085568946206974029)
                  ·
                    refine ⟨1661920532088354827615261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4431788085568946206974029 1661920532088354827615261)
                    ·
                      refine ⟨623220199533133060355723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1661920532088354827615261 623220199533133060355723)
                      ·
                        rfl

theorem cell23_1213717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_1213717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213717 prefixEnd_1213717 := by exact prefixLift 1213717
  have htrace : WordTrace (prefixWord ++ tailWord_1213717) baseStart_1213717 baseEnd_1213717 := by
    simpa [prefixWord, tailWord_1213717, baseEnd_1213717] using wordTrace_append hprefix tailTrace_1213717
  have hstable : (prefixWord ++ tailWord_1213717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213717).length < 2 ^ (prefixWord ++ tailWord_1213717).sum := by decide
  have hdescent : baseEnd_1213717 < baseStart_1213717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213738 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_1213738 : Nat := 118140960795 + 1213738 * 2 ^ 59
def prefixEnd_1213738 : Nat := 4983230072969 + 3 ^ 40 * 1213738 * 2
def baseEnd_1213738 : Nat := 623230982626877478193127

theorem tailTrace_1213738 : CollatzResearch.WordTrace tailWord_1213738 prefixEnd_1213738 623230982626877478193127 := by
  unfold tailWord_1213738
  simp only [CollatzResearch.WordTrace]
  refine ⟨11067165419210497698078467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29512441117894660528209245 11067165419210497698078467)
  ·
    refine ⟨16600748128815746547117701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11067165419210497698078467 16600748128815746547117701)
    ·
      refine ⟨3112640274152952477584569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16600748128815746547117701 3112640274152952477584569)
      ·
        refine ⟨2334480205614714358188427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3112640274152952477584569 2334480205614714358188427)
        ·
          refine ⟨3501720308422071537282641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334480205614714358188427 3501720308422071537282641)
          ·
            refine ⟨2626290231316553652961981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3501720308422071537282641 2626290231316553652961981)
            ·
              refine ⟨984858836743707619860743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2626290231316553652961981 984858836743707619860743)
              ·
                refine ⟨1477288255115561429791115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984858836743707619860743 1477288255115561429791115)
                ·
                  refine ⟨2215932382673342144686673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477288255115561429791115 2215932382673342144686673)
                  ·
                    refine ⟨1661949287005006608515005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2215932382673342144686673 1661949287005006608515005)
                    ·
                      refine ⟨623230982626877478193127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1661949287005006608515005 623230982626877478193127)
                      ·
                        rfl

theorem cell23_1213738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_1213738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213738 prefixEnd_1213738 := by exact prefixLift 1213738
  have htrace : WordTrace (prefixWord ++ tailWord_1213738) baseStart_1213738 baseEnd_1213738 := by
    simpa [prefixWord, tailWord_1213738, baseEnd_1213738] using wordTrace_append hprefix tailTrace_1213738
  have hstable : (prefixWord ++ tailWord_1213738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213738).length < 2 ^ (prefixWord ++ tailWord_1213738).sum := by decide
  have hdescent : baseEnd_1213738 < baseStart_1213738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213761 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1213761 : Nat := 118140960795 + 1213761 * 2 ^ 59
def prefixEnd_1213761 : Nat := 4983230072969 + 3 ^ 40 * 1213761 * 2
def baseEnd_1213761 : Nat := 623242792681930888205521

theorem tailTrace_1213761 : CollatzResearch.WordTrace tailWord_1213761 prefixEnd_1213761 623242792681930888205521 := by
  unfold tailWord_1213761
  simp only [CollatzResearch.WordTrace]
  refine ⟨44269500555758665720401137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29513000370505777146934091 44269500555758665720401137)
  ·
    refine ⟨33202125416818999290300853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44269500555758665720401137 33202125416818999290300853)
    ·
      refine ⟨3112699257826781183465705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33202125416818999290300853 3112699257826781183465705)
      ·
        refine ⟨2334524443370085887599279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3112699257826781183465705 2334524443370085887599279)
        ·
          refine ⟨3501786665055128831398919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334524443370085887599279 3501786665055128831398919)
          ·
            refine ⟨5252679997582693247098379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501786665055128831398919 5252679997582693247098379)
            ·
              refine ⟨7879019996374039870647569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5252679997582693247098379 7879019996374039870647569)
              ·
                refine ⟨5909264997280529902985677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7879019996374039870647569 5909264997280529902985677)
                ·
                  refine ⟨2215974373980198713619629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5909264997280529902985677 2215974373980198713619629)
                  ·
                    refine ⟨830990390242574517607361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2215974373980198713619629 830990390242574517607361)
                    ·
                      refine ⟨623242792681930888205521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 830990390242574517607361 623242792681930888205521)
                      ·
                        rfl

theorem cell23_1213761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1213761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213761 prefixEnd_1213761 := by exact prefixLift 1213761
  have htrace : WordTrace (prefixWord ++ tailWord_1213761) baseStart_1213761 baseEnd_1213761 := by
    simpa [prefixWord, tailWord_1213761, baseEnd_1213761] using wordTrace_append hprefix tailTrace_1213761
  have hstable : (prefixWord ++ tailWord_1213761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213761).length < 2 ^ (prefixWord ++ tailWord_1213761).sum := by decide
  have hdescent : baseEnd_1213761 < baseStart_1213761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213767 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 2, 6]
def baseStart_1213767 : Nat := 118140960795 + 1213767 * 2 ^ 59
def prefixEnd_1213767 : Nat := 4983230072969 + 3 ^ 40 * 1213767 * 2
def baseEnd_1213767 : Nat := 207748624521952621576831

theorem tailTrace_1213767 : CollatzResearch.WordTrace tailWord_1213767 prefixEnd_1213767 207748624521952621576831 := by
  unfold tailWord_1213767
  simp only [CollatzResearch.WordTrace]
  refine ⟨44269719393736928745119555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29513146262491285830079703 44269719393736928745119555)
  ·
    refine ⟨66404579090605393117679333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44269719393736928745119555 66404579090605393117679333)
    ·
      refine ⟨12450858579488511209564875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66404579090605393117679333 12450858579488511209564875)
      ·
        refine ⟨18676287869232766814347313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12450858579488511209564875 18676287869232766814347313)
        ·
          refine ⟨14007215901924575110760485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18676287869232766814347313 14007215901924575110760485)
          ·
            refine ⟨2626352981610857833267591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14007215901924575110760485 2626352981610857833267591)
            ·
              refine ⟨3939529472416286749901387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626352981610857833267591 3939529472416286749901387)
              ·
                refine ⟨5909294208624430124852081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939529472416286749901387 5909294208624430124852081)
                ·
                  refine ⟨4431970656468322593639061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5909294208624430124852081 4431970656468322593639061)
                  ·
                    refine ⟨207748624521952621576831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4431970656468322593639061 207748624521952621576831)
                    ·
                      rfl

theorem cell23_1213767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_1213767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213767 prefixEnd_1213767 := by exact prefixLift 1213767
  have htrace : WordTrace (prefixWord ++ tailWord_1213767) baseStart_1213767 baseEnd_1213767 := by
    simpa [prefixWord, tailWord_1213767, baseEnd_1213767] using wordTrace_append hprefix tailTrace_1213767
  have hstable : (prefixWord ++ tailWord_1213767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213767).length < 2 ^ (prefixWord ++ tailWord_1213767).sum := by decide
  have hdescent : baseEnd_1213767 < baseStart_1213767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213777 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_1213777 : Nat := 118140960795 + 1213777 * 2 ^ 59
def prefixEnd_1213777 : Nat := 4983230072969 + 3 ^ 40 * 1213777 * 2
def baseEnd_1213777 : Nat := 623251008372402825605447

theorem tailTrace_1213777 : CollatzResearch.WordTrace tailWord_1213777 prefixEnd_1213777 623251008372402825605447 := by
  unfold tailWord_1213777
  simp only [CollatzResearch.WordTrace]
  refine ⟨44270084123700700452983585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29513389415800466968655723 44270084123700700452983585)
  ·
    refine ⟨33202563092775525339737689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44270084123700700452983585 33202563092775525339737689)
    ·
      refine ⟨24901922319581644004803267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33202563092775525339737689 24901922319581644004803267)
      ·
        refine ⟨37352883479372466007204901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24901922319581644004803267 37352883479372466007204901)
        ·
          refine ⟨7003665652382337376350919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37352883479372466007204901 7003665652382337376350919)
          ·
            refine ⟨10505498478573506064526379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7003665652382337376350919 10505498478573506064526379)
            ·
              refine ⟨15758247717860259096789569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10505498478573506064526379 15758247717860259096789569)
              ·
                refine ⟨11818685788395194322592177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15758247717860259096789569 11818685788395194322592177)
                ·
                  refine ⟨8864014341296395741944133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11818685788395194322592177 8864014341296395741944133)
                  ·
                    refine ⟨1662002688993074201614525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8864014341296395741944133 1662002688993074201614525)
                    ·
                      refine ⟨623251008372402825605447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1662002688993074201614525 623251008372402825605447)
                      ·
                        rfl

theorem cell23_1213777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_1213777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213777 prefixEnd_1213777 := by exact prefixLift 1213777
  have htrace : WordTrace (prefixWord ++ tailWord_1213777) baseStart_1213777 baseEnd_1213777 := by
    simpa [prefixWord, tailWord_1213777, baseEnd_1213777] using wordTrace_append hprefix tailTrace_1213777
  have hstable : (prefixWord ++ tailWord_1213777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213777).length < 2 ^ (prefixWord ++ tailWord_1213777).sum := by decide
  have hdescent : baseEnd_1213777 < baseStart_1213777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213789 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1213789 : Nat := 118140960795 + 1213789 * 2 ^ 59
def prefixEnd_1213789 : Nat := 4983230072969 + 3 ^ 40 * 1213789 * 2
def baseEnd_1213789 : Nat := 623257170140256778655393

theorem tailTrace_1213789 : CollatzResearch.WordTrace tailWord_1213789 prefixEnd_1213789 623257170140256778655393 := by
  unfold tailWord_1213789
  simp only [CollatzResearch.WordTrace]
  refine ⟨44270521799657226502420421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29513681199771484334946947 44270521799657226502420421)
  ·
    refine ⟨8300722837435729969203829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44270521799657226502420421 8300722837435729969203829)
    ·
      refine ⟨778192766009599684612859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8300722837435729969203829 778192766009599684612859)
      ·
        refine ⟨1167289149014399526919289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778192766009599684612859 1167289149014399526919289)
        ·
          refine ⟨875466861760799645189467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1167289149014399526919289 875466861760799645189467)
          ·
            refine ⟨1313200292641199467784201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875466861760799645189467 1313200292641199467784201)
            ·
              refine ⟨984900219480899600838151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313200292641199467784201 984900219480899600838151)
              ·
                refine ⟨1477350329221349401257227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984900219480899600838151 1477350329221349401257227)
                ·
                  refine ⟨2216025493832024101885841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477350329221349401257227 2216025493832024101885841)
                  ·
                    refine ⟨1662019120374018076414381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2216025493832024101885841 1662019120374018076414381)
                    ·
                      refine ⟨623257170140256778655393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1662019120374018076414381 623257170140256778655393)
                      ·
                        rfl

theorem cell23_1213789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1213789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213789 prefixEnd_1213789 := by exact prefixLift 1213789
  have htrace : WordTrace (prefixWord ++ tailWord_1213789) baseStart_1213789 baseEnd_1213789 := by
    simpa [prefixWord, tailWord_1213789, baseEnd_1213789] using wordTrace_append hprefix tailTrace_1213789
  have hstable : (prefixWord ++ tailWord_1213789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213789).length < 2 ^ (prefixWord ++ tailWord_1213789).sum := by decide
  have hdescent : baseEnd_1213789 < baseStart_1213789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213807 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 3]
def baseStart_1213807 : Nat := 118140960795 + 1213807 * 2 ^ 59
def prefixEnd_1213807 : Nat := 4983230072969 + 3 ^ 40 * 1213807 * 2
def baseEnd_1213807 : Nat := 623266412792037708230309

theorem tailTrace_1213807 : CollatzResearch.WordTrace tailWord_1213807 prefixEnd_1213807 623266412792037708230309 := by
  unfold tailWord_1213807
  simp only [CollatzResearch.WordTrace]
  refine ⟨44271178313592015576575675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29514118875728010384383783 44271178313592015576575675)
  ·
    refine ⟨66406767470388023364863513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44271178313592015576575675 66406767470388023364863513)
    ·
      refine ⟨49805075602791017523647635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66406767470388023364863513 49805075602791017523647635)
      ·
        refine ⟨74707613404186526285471453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49805075602791017523647635 74707613404186526285471453)
        ·
          refine ⟨28015355026569947357051795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74707613404186526285471453 28015355026569947357051795)
          ·
            refine ⟨42023032539854921035577693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28015355026569947357051795 42023032539854921035577693)
            ·
              refine ⟨15758637202445595388341635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42023032539854921035577693 15758637202445595388341635)
              ·
                refine ⟨23637955803668393082512453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15758637202445595388341635 23637955803668393082512453)
                ·
                  refine ⟨4432116713187823702971085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23637955803668393082512453 4432116713187823702971085)
                  ·
                    refine ⟨1662043767445433888614157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4432116713187823702971085 1662043767445433888614157)
                    ·
                      refine ⟨623266412792037708230309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1662043767445433888614157 623266412792037708230309)
                      ·
                        rfl

theorem cell23_1213807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_1213807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213807 prefixEnd_1213807 := by exact prefixLift 1213807
  have htrace : WordTrace (prefixWord ++ tailWord_1213807) baseStart_1213807 baseEnd_1213807 := by
    simpa [prefixWord, tailWord_1213807, baseEnd_1213807] using wordTrace_append hprefix tailTrace_1213807
  have hstable : (prefixWord ++ tailWord_1213807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213807).length < 2 ^ (prefixWord ++ tailWord_1213807).sum := by decide
  have hdescent : baseEnd_1213807 < baseStart_1213807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213825 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_1213825 : Nat := 118140960795 + 1213825 * 2 ^ 59
def prefixEnd_1213825 : Nat := 4983230072969 + 3 ^ 40 * 1213825 * 2
def baseEnd_1213825 : Nat := 623275655443818637805227

theorem tailTrace_1213825 : CollatzResearch.WordTrace tailWord_1213825 prefixEnd_1213825 623275655443818637805227 := by
  unfold tailWord_1213825
  simp only [CollatzResearch.WordTrace]
  refine ⟨44271834827526804650730929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29514556551684536433820619 44271834827526804650730929)
  ·
    refine ⟨33203876120645103488048197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44271834827526804650730929 33203876120645103488048197)
    ·
      refine ⟨6225726772620956904009037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33203876120645103488048197 6225726772620956904009037)
      ·
        refine ⟨2334647539732858839003389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6225726772620956904009037 2334647539732858839003389)
        ·
          refine ⟨875492827399822064626271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2334647539732858839003389 875492827399822064626271)
          ·
            refine ⟨1313239241099733096939407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875492827399822064626271 1313239241099733096939407)
            ·
              refine ⟨1969858861649599645409111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313239241099733096939407 1969858861649599645409111)
              ·
                refine ⟨2954788292474399468113667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969858861649599645409111 2954788292474399468113667)
                ·
                  refine ⟨4432182438711599202170501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2954788292474399468113667 4432182438711599202170501)
                  ·
                    refine ⟨831034207258424850406969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4432182438711599202170501 831034207258424850406969)
                    ·
                      refine ⟨623275655443818637805227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831034207258424850406969 623275655443818637805227)
                      ·
                        rfl

theorem cell23_1213825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_1213825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213825 prefixEnd_1213825 := by exact prefixLift 1213825
  have htrace : WordTrace (prefixWord ++ tailWord_1213825) baseStart_1213825 baseEnd_1213825 := by
    simpa [prefixWord, tailWord_1213825, baseEnd_1213825] using wordTrace_append hprefix tailTrace_1213825
  have hstable : (prefixWord ++ tailWord_1213825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213825).length < 2 ^ (prefixWord ++ tailWord_1213825).sum := by decide
  have hdescent : baseEnd_1213825 < baseStart_1213825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213827 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 1, 7]
def baseStart_1213827 : Nat := 118140960795 + 1213827 * 2 ^ 59
def prefixEnd_1213827 : Nat := 4983230072969 + 3 ^ 40 * 1213827 * 2
def baseEnd_1213827 : Nat := 207758894135042543326739

theorem tailTrace_1213827 : CollatzResearch.WordTrace tailWord_1213827 prefixEnd_1213827 207758894135042543326739 := by
  unfold tailWord_1213827
  simp only [CollatzResearch.WordTrace]
  refine ⟨44271907773519558992303735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29514605182346372661535823 44271907773519558992303735)
  ·
    refine ⟨66407861660279338488455603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44271907773519558992303735 66407861660279338488455603)
    ·
      refine ⟨99611792490419007732683405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66407861660279338488455603 99611792490419007732683405)
      ·
        refine ⟨37354422183907127899756277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99611792490419007732683405 37354422183907127899756277)
        ·
          refine ⟨3501977079741293240602151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37354422183907127899756277 3501977079741293240602151)
          ·
            refine ⟨5252965619611939860903227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501977079741293240602151 5252965619611939860903227)
            ·
              refine ⟨7879448429417909791354841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5252965619611939860903227 7879448429417909791354841)
              ·
                refine ⟨5909586322063432343516131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7879448429417909791354841 5909586322063432343516131)
                ·
                  refine ⟨8864379483095148515274197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5909586322063432343516131 8864379483095148515274197)
                  ·
                    refine ⟨207758894135042543326739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8864379483095148515274197 207758894135042543326739)
                    ·
                      rfl

theorem cell23_1213827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 7].length) (baseStart_1213827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213827 prefixEnd_1213827 := by exact prefixLift 1213827
  have htrace : WordTrace (prefixWord ++ tailWord_1213827) baseStart_1213827 baseEnd_1213827 := by
    simpa [prefixWord, tailWord_1213827, baseEnd_1213827] using wordTrace_append hprefix tailTrace_1213827
  have hstable : (prefixWord ++ tailWord_1213827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213827).length < 2 ^ (prefixWord ++ tailWord_1213827).sum := by decide
  have hdescent : baseEnd_1213827 < baseStart_1213827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213844 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_1213844 : Nat := 118140960795 + 1213844 * 2 ^ 59
def prefixEnd_1213844 : Nat := 4983230072969 + 3 ^ 40 * 1213844 * 2
def baseEnd_1213844 : Nat := 207761803858751354489213

theorem tailTrace_1213844 : CollatzResearch.WordTrace tailWord_1213844 prefixEnd_1213844 207761803858751354489213 := by
  unfold tailWord_1213844
  simp only [CollatzResearch.WordTrace]
  refine ⟨22136263907228985447836293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29515018542971980597115057 22136263907228985447836293)
  ·
    refine ⟨4150549482605434771469305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22136263907228985447836293 4150549482605434771469305)
    ·
      refine ⟨3112912111954076078601979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4150549482605434771469305 3112912111954076078601979)
      ·
        refine ⟨4669368167931114117902969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3112912111954076078601979 4669368167931114117902969)
        ·
          refine ⟨3502026125948335588427227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4669368167931114117902969 3502026125948335588427227)
          ·
            refine ⟨5253039188922503382640841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502026125948335588427227 5253039188922503382640841)
            ·
              refine ⟨3939779391691877536980631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5253039188922503382640841 3939779391691877536980631)
              ·
                refine ⟨5909669087537816305470947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3939779391691877536980631 5909669087537816305470947)
                ·
                  refine ⟨8864503631306724458206421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5909669087537816305470947 8864503631306724458206421)
                  ·
                    refine ⟨207761803858751354489213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8864503631306724458206421 207761803858751354489213)
                    ·
                      rfl

theorem cell23_1213844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_1213844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213844 prefixEnd_1213844 := by exact prefixLift 1213844
  have htrace : WordTrace (prefixWord ++ tailWord_1213844) baseStart_1213844 baseEnd_1213844 := by
    simpa [prefixWord, tailWord_1213844, baseEnd_1213844] using wordTrace_append hprefix tailTrace_1213844
  have hstable : (prefixWord ++ tailWord_1213844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213844).length < 2 ^ (prefixWord ++ tailWord_1213844).sum := by decide
  have hdescent : baseEnd_1213844 < baseStart_1213844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213848 : List Nat := [2, 1, 2, 5, 2, 2, 1, 3, 5]
def baseStart_1213848 : Nat := 118140960795 + 1213848 * 2 ^ 59
def prefixEnd_1213848 : Nat := 4983230072969 + 3 ^ 40 * 1213848 * 2
def baseEnd_1213848 : Nat := 69254162833208005313069

theorem tailTrace_1213848 : CollatzResearch.WordTrace tailWord_1213848 prefixEnd_1213848 69254162833208005313069 := by
  unfold tailWord_1213848
  simp only [CollatzResearch.WordTrace]
  refine ⟨22136336853221739789409099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29515115804295653052545465 22136336853221739789409099)
  ·
    refine ⟨33204505279832609684113649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22136336853221739789409099 33204505279832609684113649)
    ·
      refine ⟨24903378959874457263085237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33204505279832609684113649 24903378959874457263085237)
      ·
        refine ⟨2334691777488230368414241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24903378959874457263085237 2334691777488230368414241)
        ·
          refine ⟨1751018833116172776310681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2334691777488230368414241 1751018833116172776310681)
          ·
            refine ⟨1313264124837129582233011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1751018833116172776310681 1313264124837129582233011)
            ·
              refine ⟨1969896187255694373349517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313264124837129582233011 1969896187255694373349517)
              ·
                refine ⟨738711070220885390006069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1969896187255694373349517 738711070220885390006069)
                ·
                  refine ⟨69254162833208005313069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 738711070220885390006069 69254162833208005313069)
                  ·
                    rfl

theorem cell23_1213848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 5].length) (baseStart_1213848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213848 prefixEnd_1213848 := by exact prefixLift 1213848
  have htrace : WordTrace (prefixWord ++ tailWord_1213848) baseStart_1213848 baseEnd_1213848 := by
    simpa [prefixWord, tailWord_1213848, baseEnd_1213848] using wordTrace_append hprefix tailTrace_1213848
  have hstable : (prefixWord ++ tailWord_1213848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213848).length < 2 ^ (prefixWord ++ tailWord_1213848).sum := by decide
  have hdescent : baseEnd_1213848 < baseStart_1213848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213874 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_1213874 : Nat := 118140960795 + 1213874 * 2 ^ 59
def prefixEnd_1213874 : Nat := 4983230072969 + 3 ^ 40 * 1213874 * 2
def baseEnd_1213874 : Nat := 207766938665296315364167

theorem tailTrace_1213874 : CollatzResearch.WordTrace tailWord_1213874 prefixEnd_1213874 207766938665296315364167 := by
  unfold tailWord_1213874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11068405501087321504816169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29515748002899524012843117 11068405501087321504816169)
  ·
    refine ⟨8301304125815491128612127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11068405501087321504816169 8301304125815491128612127)
    ·
      refine ⟨12451956188723236692918191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8301304125815491128612127 12451956188723236692918191)
      ·
        refine ⟨18677934283084855039377287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12451956188723236692918191 18677934283084855039377287)
        ·
          refine ⟨28016901424627282559065931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18677934283084855039377287 28016901424627282559065931)
          ·
            refine ⟨42025352136940923838598897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28016901424627282559065931 42025352136940923838598897)
            ·
              refine ⟨31519014102705692878949173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42025352136940923838598897 31519014102705692878949173)
              ·
                refine ⟨2954907572128658707401485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31519014102705692878949173 2954907572128658707401485)
                ·
                  refine ⟨1108090339548247015275557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2954907572128658707401485 1108090339548247015275557)
                  ·
                    refine ⟨207766938665296315364167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1108090339548247015275557 207766938665296315364167)
                    ·
                      rfl

theorem cell23_1213874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_1213874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213874 prefixEnd_1213874 := by exact prefixLift 1213874
  have htrace : WordTrace (prefixWord ++ tailWord_1213874) baseStart_1213874 baseEnd_1213874 := by
    simpa [prefixWord, tailWord_1213874, baseEnd_1213874] using wordTrace_append hprefix tailTrace_1213874
  have hstable : (prefixWord ++ tailWord_1213874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213874).length < 2 ^ (prefixWord ++ tailWord_1213874).sum := by decide
  have hdescent : baseEnd_1213874 < baseStart_1213874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213925 : List Nat := [1, 3, 1, 5, 1, 1, 4, 2, 1, 4]
def baseStart_1213925 : Nat := 118140960795 + 1213925 * 2 ^ 59
def prefixEnd_1213925 : Nat := 4983230072969 + 3 ^ 40 * 1213925 * 2
def baseEnd_1213925 : Nat := 207775667836422748851589

theorem tailTrace_1213925 : CollatzResearch.WordTrace tailWord_1213925 prefixEnd_1213925 207775667836422748851589 := by
  unfold tailWord_1213925
  simp only [CollatzResearch.WordTrace]
  refine ⟨44275482127164521729371229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29516988084776347819580819 44275482127164521729371229)
  ·
    refine ⟨16603305797686695648514211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44275482127164521729371229 16603305797686695648514211)
    ·
      refine ⟨24904958696530043472771317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16603305797686695648514211 24904958696530043472771317)
      ·
        refine ⟨2334839877799691575572311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24904958696530043472771317 2334839877799691575572311)
        ·
          refine ⟨3502259816699537363358467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334839877799691575572311 3502259816699537363358467)
          ·
            refine ⟨5253389725049306045037701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3502259816699537363358467 5253389725049306045037701)
            ·
              refine ⟨985010573446744883444569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5253389725049306045037701 985010573446744883444569)
              ·
                refine ⟨738757930085058662583427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985010573446744883444569 738757930085058662583427)
                ·
                  refine ⟨1108136895127587993875141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738757930085058662583427 1108136895127587993875141)
                  ·
                    refine ⟨207775667836422748851589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1108136895127587993875141 207775667836422748851589)
                    ·
                      rfl

theorem cell23_1213925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_1213925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213925 prefixEnd_1213925 := by exact prefixLift 1213925
  have htrace : WordTrace (prefixWord ++ tailWord_1213925) baseStart_1213925 baseEnd_1213925 := by
    simpa [prefixWord, tailWord_1213925, baseEnd_1213925] using wordTrace_append hprefix tailTrace_1213925
  have hstable : (prefixWord ++ tailWord_1213925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213925).length < 2 ^ (prefixWord ++ tailWord_1213925).sum := by decide
  have hdescent : baseEnd_1213925 < baseStart_1213925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213934 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 5, 5]
def baseStart_1213934 : Nat := 118140960795 + 1213934 * 2 ^ 59
def prefixEnd_1213934 : Nat := 4983230072969 + 3 ^ 40 * 1213934 * 2
def baseEnd_1213934 : Nat := 207777208278386237114075

theorem tailTrace_1213934 : CollatzResearch.WordTrace tailWord_1213934 prefixEnd_1213934 207777208278386237114075 := by
  unfold tailWord_1213934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534476298016489533306107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29517206922754610844299237 5534476298016489533306107)
  ·
    refine ⟨8301714447024734299959161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5534476298016489533306107 8301714447024734299959161)
    ·
      refine ⟨6226285835268550724969371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8301714447024734299959161 6226285835268550724969371)
      ·
        refine ⟨9339428752902826087454057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6226285835268550724969371 9339428752902826087454057)
        ·
          refine ⟨7004571564677119565590543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9339428752902826087454057 7004571564677119565590543)
          ·
            refine ⟨10506857347015679348385815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7004571564677119565590543 10506857347015679348385815)
            ·
              refine ⟨15760286020523519022578723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10506857347015679348385815 15760286020523519022578723)
              ·
                refine ⟨23640429030785278533868085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15760286020523519022578723 23640429030785278533868085)
                ·
                  refine ⟨2216290221636119862550133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23640429030785278533868085 2216290221636119862550133)
                  ·
                    refine ⟨207777208278386237114075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2216290221636119862550133 207777208278386237114075)
                    ·
                      rfl

theorem cell23_1213934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_1213934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213934 prefixEnd_1213934 := by exact prefixLift 1213934
  have htrace : WordTrace (prefixWord ++ tailWord_1213934) baseStart_1213934 baseEnd_1213934 := by
    simpa [prefixWord, tailWord_1213934, baseEnd_1213934] using wordTrace_append hprefix tailTrace_1213934
  have hstable : (prefixWord ++ tailWord_1213934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213934).length < 2 ^ (prefixWord ++ tailWord_1213934).sum := by decide
  have hdescent : baseEnd_1213934 < baseStart_1213934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213947 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 5, 6]
def baseStart_1213947 : Nat := 118140960795 + 1213947 * 2 ^ 59
def prefixEnd_1213947 : Nat := 4983230072969 + 3 ^ 40 * 1213947 * 2
def baseEnd_1213947 : Nat := 207779433361222386826555

theorem tailTrace_1213947 : CollatzResearch.WordTrace tailWord_1213947 prefixEnd_1213947 207779433361222386826555 := by
  unfold tailWord_1213947
  simp only [CollatzResearch.WordTrace]
  refine ⟨44276284533084819486672095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29517523022056546324448063 44276284533084819486672095)
  ·
    refine ⟨66414426799627229230008143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44276284533084819486672095 66414426799627229230008143)
    ·
      refine ⟨99621640199440843845012215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66414426799627229230008143 99621640199440843845012215)
      ·
        refine ⟨149432460299161265767518323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99621640199440843845012215 149432460299161265767518323)
        ·
          refine ⟨224148690448741898651277485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149432460299161265767518323 224148690448741898651277485)
          ·
            refine ⟨84055758918278211994229057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224148690448741898651277485 84055758918278211994229057)
            ·
              refine ⟨63041819188708658995671793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84055758918278211994229057 63041819188708658995671793)
              ·
                refine ⟨47281364391531494246753845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63041819188708658995671793 47281364391531494246753845)
                ·
                  refine ⟨4432627911706077585633173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47281364391531494246753845 4432627911706077585633173)
                  ·
                    refine ⟨207779433361222386826555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4432627911706077585633173 207779433361222386826555)
                    ·
                      rfl

theorem cell23_1213947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 6].length) (baseStart_1213947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213947 prefixEnd_1213947 := by exact prefixLift 1213947
  have htrace : WordTrace (prefixWord ++ tailWord_1213947) baseStart_1213947 baseEnd_1213947 := by
    simpa [prefixWord, tailWord_1213947, baseEnd_1213947] using wordTrace_append hprefix tailTrace_1213947
  have hstable : (prefixWord ++ tailWord_1213947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213947).length < 2 ^ (prefixWord ++ tailWord_1213947).sum := by decide
  have hdescent : baseEnd_1213947 < baseStart_1213947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213971 : List Nat := [1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 4]
def baseStart_1213971 : Nat := 118140960795 + 1213971 * 2 ^ 59
def prefixEnd_1213971 : Nat := 4983230072969 + 3 ^ 40 * 1213971 * 2
def baseEnd_1213971 : Nat := 623350623619375066579555

theorem tailTrace_1213971 : CollatzResearch.WordTrace tailWord_1213971 prefixEnd_1213971 623350623619375066579555 := by
  unfold tailWord_1213971
  simp only [CollatzResearch.WordTrace]
  refine ⟨44277159884997871585545767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29518106589998581057030511 44277159884997871585545767)
  ·
    refine ⟨66415739827496807378318651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44277159884997871585545767 66415739827496807378318651)
    ·
      refine ⟨99623609741245211067477977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66415739827496807378318651 99623609741245211067477977)
      ·
        refine ⟨74717707305933908300608483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99623609741245211067477977 74717707305933908300608483)
        ·
          refine ⟨112076560958900862450912725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74717707305933908300608483 112076560958900862450912725)
          ·
            refine ⟨2626794397474238963693267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 112076560958900862450912725 2626794397474238963693267)
            ·
              refine ⟨3940191596211358445539901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626794397474238963693267 3940191596211358445539901)
              ·
                refine ⟨1477571848579259417077463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3940191596211358445539901 1477571848579259417077463)
                ·
                  refine ⟨2216357772868889125616195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477571848579259417077463 2216357772868889125616195)
                  ·
                    refine ⟨3324536659303333688424293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2216357772868889125616195 3324536659303333688424293)
                    ·
                      refine ⟨623350623619375066579555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3324536659303333688424293 623350623619375066579555)
                      ·
                        rfl

theorem cell23_1213971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 4].length) (baseStart_1213971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213971 prefixEnd_1213971 := by exact prefixLift 1213971
  have htrace : WordTrace (prefixWord ++ tailWord_1213971) baseStart_1213971 baseEnd_1213971 := by
    simpa [prefixWord, tailWord_1213971, baseEnd_1213971] using wordTrace_append hprefix tailTrace_1213971
  have hstable : (prefixWord ++ tailWord_1213971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213971).length < 2 ^ (prefixWord ++ tailWord_1213971).sum := by decide
  have hdescent : baseEnd_1213971 < baseStart_1213971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213981 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1213981 : Nat := 118140960795 + 1213981 * 2 ^ 59
def prefixEnd_1213981 : Nat := 4983230072969 + 3 ^ 40 * 1213981 * 2
def baseEnd_1213981 : Nat := 207785252808640009151503

theorem tailTrace_1213981 : CollatzResearch.WordTrace tailWord_1213981 prefixEnd_1213981 207785252808640009151503 := by
  unfold tailWord_1213981
  simp only [CollatzResearch.WordTrace]
  refine ⟨44277524614961643293409797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29518349743307762195606531 44277524614961643293409797)
  ·
    refine ⟨8302035865305308117514337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44277524614961643293409797 8302035865305308117514337)
    ·
      refine ⟨6226526898978981088135753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8302035865305308117514337 6226526898978981088135753)
      ·
        refine ⟨4669895174234235816101815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6226526898978981088135753 4669895174234235816101815)
        ·
          refine ⟨7004842761351353724152723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4669895174234235816101815 7004842761351353724152723)
          ·
            refine ⟨10507264142027030586229085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7004842761351353724152723 10507264142027030586229085)
            ·
              refine ⟨3940224053260136469835907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10507264142027030586229085 3940224053260136469835907)
              ·
                refine ⟨5910336079890204704753861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940224053260136469835907 5910336079890204704753861)
                ·
                  refine ⟨1108188014979413382141349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5910336079890204704753861 1108188014979413382141349)
                  ·
                    refine ⟨207785252808640009151503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1108188014979413382141349 207785252808640009151503)
                    ·
                      rfl

theorem cell23_1213981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1213981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213981 prefixEnd_1213981 := by exact prefixLift 1213981
  have htrace : WordTrace (prefixWord ++ tailWord_1213981) baseStart_1213981 baseEnd_1213981 := by
    simpa [prefixWord, tailWord_1213981, baseEnd_1213981] using wordTrace_append hprefix tailTrace_1213981
  have hstable : (prefixWord ++ tailWord_1213981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213981).length < 2 ^ (prefixWord ++ tailWord_1213981).sum := by decide
  have hdescent : baseEnd_1213981 < baseStart_1213981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213994 : List Nat := [3, 1, 4, 1, 1, 1, 2, 10]
def baseStart_1213994 : Nat := 118140960795 + 1213994 * 2 ^ 59
def prefixEnd_1213994 : Nat := 4983230072969 + 3 ^ 40 * 1213994 * 2
def baseEnd_1213994 : Nat := 23087497543497350984887

theorem tailTrace_1213994 : CollatzResearch.WordTrace tailWord_1213994 prefixEnd_1213994 23087497543497350984887 := by
  unfold tailWord_1213994
  simp only [CollatzResearch.WordTrace]
  refine ⟨11069499690978636628408259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29518665842609697675755357 11069499690978636628408259)
  ·
    refine ⟨16604249536467954942612389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11069499690978636628408259 16604249536467954942612389)
    ·
      refine ⟨3113296788087741551739823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16604249536467954942612389 3113296788087741551739823)
      ·
        refine ⟨4669945182131612327609735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113296788087741551739823 4669945182131612327609735)
        ·
          refine ⟨7004917773197418491414603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4669945182131612327609735 7004917773197418491414603)
          ·
            refine ⟨10507376659796127737121905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7004917773197418491414603 10507376659796127737121905)
            ·
              refine ⟨7880532494847095802841429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10507376659796127737121905 7880532494847095802841429)
              ·
                refine ⟨23087497543497350984887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7880532494847095802841429 23087497543497350984887)
                ·
                  rfl

theorem cell23_1213994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 10].length) (baseStart_1213994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213994 prefixEnd_1213994 := by exact prefixLift 1213994
  have htrace : WordTrace (prefixWord ++ tailWord_1213994) baseStart_1213994 baseEnd_1213994 := by
    simpa [prefixWord, tailWord_1213994, baseEnd_1213994] using wordTrace_append hprefix tailTrace_1213994
  have hstable : (prefixWord ++ tailWord_1213994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213994).length < 2 ^ (prefixWord ++ tailWord_1213994).sum := by decide
  have hdescent : baseEnd_1213994 < baseStart_1213994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213998 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_1213998 : Nat := 118140960795 + 1213998 * 2 ^ 59
def prefixEnd_1213998 : Nat := 4983230072969 + 3 ^ 40 * 1213998 * 2
def baseEnd_1213998 : Nat := 207788162532348820313977

theorem tailTrace_1213998 : CollatzResearch.WordTrace tailWord_1213998 prefixEnd_1213998 207788162532348820313977 := by
  unfold tailWord_1213998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5534768081987506899597331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29518763103933370131185765 5534768081987506899597331)
  ·
    refine ⟨8302152122981260349395997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5534768081987506899597331 8302152122981260349395997)
    ·
      refine ⟨3113307046117972631023499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8302152122981260349395997 3113307046117972631023499)
      ·
        refine ⟨4669960569176958946535249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113307046117972631023499 4669960569176958946535249)
        ·
          refine ⟨3502470426882719209901437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4669960569176958946535249 3502470426882719209901437)
          ·
            refine ⟨1313426410081019703713039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3502470426882719209901437 1313426410081019703713039)
            ·
              refine ⟨1970139615121529555569559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313426410081019703713039 1970139615121529555569559)
              ·
                refine ⟨2955209422682294333354339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970139615121529555569559 2955209422682294333354339)
                ·
                  refine ⟨4432814134023441500031509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955209422682294333354339 4432814134023441500031509)
                  ·
                    refine ⟨207788162532348820313977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4432814134023441500031509 207788162532348820313977)
                    ·
                      rfl

theorem cell23_1213998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_1213998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1213998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1213998 prefixEnd_1213998 := by exact prefixLift 1213998
  have htrace : WordTrace (prefixWord ++ tailWord_1213998) baseStart_1213998 baseEnd_1213998 := by
    simpa [prefixWord, tailWord_1213998, baseEnd_1213998] using wordTrace_append hprefix tailTrace_1213998
  have hstable : (prefixWord ++ tailWord_1213998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213998).length < 2 ^ (prefixWord ++ tailWord_1213998).sum := by decide
  have hdescent : baseEnd_1213998 < baseStart_1213998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214008 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3]
def baseStart_1214008 : Nat := 118140960795 + 1214008 * 2 ^ 59
def prefixEnd_1214008 : Nat := 4983230072969 + 3 ^ 40 * 1214008 * 2
def baseEnd_1214008 : Nat := 623369622403591421816885

theorem tailTrace_1214008 : CollatzResearch.WordTrace tailWord_1214008 prefixEnd_1214008 623369622403591421816885 := by
  unfold tailWord_1214008
  simp only [CollatzResearch.WordTrace]
  refine ⟨22139254692931913452321339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29519006257242551269761785 22139254692931913452321339)
  ·
    refine ⟨33208882039397870178482009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22139254692931913452321339 33208882039397870178482009)
    ·
      refine ⟨24906661529548402633861507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33208882039397870178482009 24906661529548402633861507)
      ·
        refine ⟨37359992294322603950792261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24906661529548402633861507 37359992294322603950792261)
        ·
          refine ⟨7004998555185488240773549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37359992294322603950792261 7004998555185488240773549)
          ·
            refine ⟨2626874458194558090290081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7004998555185488240773549 2626874458194558090290081)
            ·
              refine ⟨1970155843645918567717561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2626874458194558090290081 1970155843645918567717561)
              ·
                refine ⟨1477616882734438925788171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970155843645918567717561 1477616882734438925788171)
                ·
                  refine ⟨2216425324101658388682257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1477616882734438925788171 2216425324101658388682257)
                  ·
                    refine ⟨1662318993076243791511693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2216425324101658388682257 1662318993076243791511693)
                    ·
                      refine ⟨623369622403591421816885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1662318993076243791511693 623369622403591421816885)
                      ·
                        rfl

theorem cell23_1214008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_1214008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214008 prefixEnd_1214008 := by exact prefixLift 1214008
  have htrace : WordTrace (prefixWord ++ tailWord_1214008) baseStart_1214008 baseEnd_1214008 := by
    simpa [prefixWord, tailWord_1214008, baseEnd_1214008] using wordTrace_append hprefix tailTrace_1214008
  have hstable : (prefixWord ++ tailWord_1214008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214008).length < 2 ^ (prefixWord ++ tailWord_1214008).sum := by decide
  have hdescent : baseEnd_1214008 < baseStart_1214008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214021 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 3]
def baseStart_1214021 : Nat := 118140960795 + 1214021 * 2 ^ 59
def prefixEnd_1214021 : Nat := 4983230072969 + 3 ^ 40 * 1214021 * 2
def baseEnd_1214021 : Nat := 623376297652099870954325

theorem tailTrace_1214021 : CollatzResearch.WordTrace tailWord_1214021 prefixEnd_1214021 623376297652099870954325 := by
  unfold tailWord_1214021
  simp only [CollatzResearch.WordTrace]
  refine ⟨44278983534816730124865917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29519322356544486749910611 44278983534816730124865917)
  ·
    refine ⟨16604618825556273796824719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44278983534816730124865917 16604618825556273796824719)
    ·
      refine ⟨24906928238334410695237079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16604618825556273796824719 24906928238334410695237079)
      ·
        refine ⟨37360392357501616042855619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24906928238334410695237079 37360392357501616042855619)
        ·
          refine ⟨56040588536252424064283429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37360392357501616042855619 56040588536252424064283429)
          ·
            refine ⟨10507610350547329512053143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56040588536252424064283429 10507610350547329512053143)
            ·
              refine ⟨15761415525820994268079715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10507610350547329512053143 15761415525820994268079715)
              ·
                refine ⟨23642123288731491402119573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15761415525820994268079715 23642123288731491402119573)
                ·
                  refine ⟨1108224529159288659474355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23642123288731491402119573 1108224529159288659474355)
                  ·
                    refine ⟨1662336793738932989211533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1108224529159288659474355 1662336793738932989211533)
                    ·
                      refine ⟨623376297652099870954325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1662336793738932989211533 623376297652099870954325)
                      ·
                        rfl

theorem cell23_1214021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_1214021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214021 prefixEnd_1214021 := by exact prefixLift 1214021
  have htrace : WordTrace (prefixWord ++ tailWord_1214021) baseStart_1214021 baseEnd_1214021 := by
    simpa [prefixWord, tailWord_1214021, baseEnd_1214021] using wordTrace_append hprefix tailTrace_1214021
  have hstable : (prefixWord ++ tailWord_1214021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214021).length < 2 ^ (prefixWord ++ tailWord_1214021).sum := by decide
  have hdescent : baseEnd_1214021 < baseStart_1214021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214031 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 5, 3, 2]
def baseStart_1214031 : Nat := 118140960795 + 1214031 * 2 ^ 59
def prefixEnd_1214031 : Nat := 4983230072969 + 3 ^ 40 * 1214031 * 2
def baseEnd_1214031 : Nat := 623381432458644831829279

theorem tailTrace_1214031 : CollatzResearch.WordTrace tailWord_1214031 prefixEnd_1214031 623381432458644831829279 := by
  unfold tailWord_1214031
  simp only [CollatzResearch.WordTrace]
  refine ⟨44279348264780501832729947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29519565509853667888486631 44279348264780501832729947)
  ·
    refine ⟨66419022397170752749094921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44279348264780501832729947 66419022397170752749094921)
    ·
      refine ⟨49814266797878064561821191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66419022397170752749094921 49814266797878064561821191)
      ·
        refine ⟨74721400196817096842731787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49814266797878064561821191 74721400196817096842731787)
        ·
          refine ⟨112082100295225645264097681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74721400196817096842731787 112082100295225645264097681)
          ·
            refine ⟨84061575221419233948073261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112082100295225645264097681 84061575221419233948073261)
            ·
              refine ⟨31523090708032212730527473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84061575221419233948073261 31523090708032212730527473)
              ·
                refine ⟨23642318031024159547895605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31523090708032212730527473 23642318031024159547895605)
                ·
                  refine ⟨2216467315408514957615213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23642318031024159547895605 2216467315408514957615213)
                  ·
                    refine ⟨831175243278193109105705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216467315408514957615213 831175243278193109105705)
                    ·
                      refine ⟨623381432458644831829279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831175243278193109105705 623381432458644831829279)
                      ·
                        rfl

theorem cell23_1214031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 3, 2].length) (baseStart_1214031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214031 prefixEnd_1214031 := by exact prefixLift 1214031
  have htrace : WordTrace (prefixWord ++ tailWord_1214031) baseStart_1214031 baseEnd_1214031 := by
    simpa [prefixWord, tailWord_1214031, baseEnd_1214031] using wordTrace_append hprefix tailTrace_1214031
  have hstable : (prefixWord ++ tailWord_1214031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214031).length < 2 ^ (prefixWord ++ tailWord_1214031).sum := by decide
  have hdescent : baseEnd_1214031 < baseStart_1214031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214055 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_1214055 : Nat := 118140960795 + 1214055 * 2 ^ 59
def prefixEnd_1214055 : Nat := 4983230072969 + 3 ^ 40 * 1214055 * 2
def baseEnd_1214055 : Nat := 623393755994352737929169

theorem tailTrace_1214055 : CollatzResearch.WordTrace tailWord_1214055 prefixEnd_1214055 623393755994352737929169 := by
  unfold tailWord_1214055
  simp only [CollatzResearch.WordTrace]
  refine ⟨44280223616693553931603619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29520149077795702621069079 44280223616693553931603619)
  ·
    refine ⟨66420335425040330897405429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44280223616693553931603619 66420335425040330897405429)
    ·
      refine ⟨6226906446097531021631759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66420335425040330897405429 6226906446097531021631759)
      ·
        refine ⟨9340359669146296532447639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6226906446097531021631759 9340359669146296532447639)
        ·
          refine ⟨14010539503719444798671459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9340359669146296532447639 14010539503719444798671459)
          ·
            refine ⟨21015809255579167198007189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14010539503719444798671459 21015809255579167198007189)
            ·
              refine ⟨985116058855273462406587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21015809255579167198007189 985116058855273462406587)
              ·
                refine ⟨1477674088282910193609881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985116058855273462406587 1477674088282910193609881)
                ·
                  refine ⟨1108255566212182645207411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1477674088282910193609881 1108255566212182645207411)
                  ·
                    refine ⟨1662383349318273967811117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1108255566212182645207411 1662383349318273967811117)
                    ·
                      refine ⟨623393755994352737929169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1662383349318273967811117 623393755994352737929169)
                      ·
                        rfl

theorem cell23_1214055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_1214055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214055 prefixEnd_1214055 := by exact prefixLift 1214055
  have htrace : WordTrace (prefixWord ++ tailWord_1214055) baseStart_1214055 baseEnd_1214055 := by
    simpa [prefixWord, tailWord_1214055, baseEnd_1214055] using wordTrace_append hprefix tailTrace_1214055
  have hstable : (prefixWord ++ tailWord_1214055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214055).length < 2 ^ (prefixWord ++ tailWord_1214055).sum := by decide
  have hdescent : baseEnd_1214055 < baseStart_1214055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214074 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_1214074 : Nat := 118140960795 + 1214074 * 2 ^ 59
def prefixEnd_1214074 : Nat := 4983230072969 + 3 ^ 40 * 1214074 * 2
def baseEnd_1214074 : Nat := 623403512126788163591581

theorem tailTrace_1214074 : CollatzResearch.WordTrace tailWord_1214074 prefixEnd_1214074 623403512126788163591581 := by
  unfold tailWord_1214074
  simp only [CollatzResearch.WordTrace]
  refine ⟨11070229150906180044136319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29520611069083146784363517 11070229150906180044136319)
  ·
    refine ⟨16605343726359270066204479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11070229150906180044136319 16605343726359270066204479)
    ·
      refine ⟨24908015589538905099306719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16605343726359270066204479 24908015589538905099306719)
      ·
        refine ⟨37362023384308357648960079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24908015589538905099306719 37362023384308357648960079)
        ·
          refine ⟨56043035076462536473440119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37362023384308357648960079 56043035076462536473440119)
          ·
            refine ⟨84064552614693804710160179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56043035076462536473440119 84064552614693804710160179)
            ·
              refine ⟨126096828922040707065240269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84064552614693804710160179 126096828922040707065240269)
              ·
                refine ⟨47286310845765265149465101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126096828922040707065240269 47286310845765265149465101)
                ·
                  refine ⟨17732366567161974431049413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47286310845765265149465101 17732366567161974431049413)
                  ·
                    refine ⟨3324818731342870205821765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17732366567161974431049413 3324818731342870205821765)
                    ·
                      refine ⟨623403512126788163591581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3324818731342870205821765 623403512126788163591581)
                      ·
                        rfl

theorem cell23_1214074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_1214074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214074 prefixEnd_1214074 := by exact prefixLift 1214074
  have htrace : WordTrace (prefixWord ++ tailWord_1214074) baseStart_1214074 baseEnd_1214074 := by
    simpa [prefixWord, tailWord_1214074, baseEnd_1214074] using wordTrace_append hprefix tailTrace_1214074
  have hstable : (prefixWord ++ tailWord_1214074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214074).length < 2 ^ (prefixWord ++ tailWord_1214074).sum := by decide
  have hdescent : baseEnd_1214074 < baseStart_1214074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214081 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1214081 : Nat := 118140960795 + 1214081 * 2 ^ 59
def prefixEnd_1214081 : Nat := 4983230072969 + 3 ^ 40 * 1214081 * 2
def baseEnd_1214081 : Nat := 623407106491369636204049

theorem tailTrace_1214081 : CollatzResearch.WordTrace tailWord_1214081 prefixEnd_1214081 623407106491369636204049 := by
  unfold tailWord_1214081
  simp only [CollatzResearch.WordTrace]
  refine ⟨44281171914599360372050097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29520781276399573581366731 44281171914599360372050097)
  ·
    refine ⟨33210878935949520279037573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44281171914599360372050097 33210878935949520279037573)
    ·
      refine ⟨6227039800490535052319545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33210878935949520279037573 6227039800490535052319545)
      ·
        refine ⟨4670279850367901289239659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6227039800490535052319545 4670279850367901289239659)
        ·
          refine ⟨7005419775551851933859489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670279850367901289239659 7005419775551851933859489)
          ·
            refine ⟨5254064831663888950394617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7005419775551851933859489 5254064831663888950394617)
            ·
              refine ⟨3940548623747916712795963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5254064831663888950394617 3940548623747916712795963)
              ·
                refine ⟨5910822935621875069193945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940548623747916712795963 5910822935621875069193945)
                ·
                  refine ⟨4433117201716406301895459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5910822935621875069193945 4433117201716406301895459)
                  ·
                    refine ⟨6649675802574609452843189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4433117201716406301895459 6649675802574609452843189)
                    ·
                      refine ⟨623407106491369636204049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6649675802574609452843189 623407106491369636204049)
                      ·
                        rfl

theorem cell23_1214081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1214081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214081 prefixEnd_1214081 := by exact prefixLift 1214081
  have htrace : WordTrace (prefixWord ++ tailWord_1214081) baseStart_1214081 baseEnd_1214081 := by
    simpa [prefixWord, tailWord_1214081, baseEnd_1214081] using wordTrace_append hprefix tailTrace_1214081
  have hstable : (prefixWord ++ tailWord_1214081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214081).length < 2 ^ (prefixWord ++ tailWord_1214081).sum := by decide
  have hdescent : baseEnd_1214081 < baseStart_1214081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214108 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1214108 : Nat := 118140960795 + 1214108 * 2 ^ 59
def prefixEnd_1214108 : Nat := 4983230072969 + 3 ^ 40 * 1214108 * 2
def baseEnd_1214108 : Nat := 623420970469041030566425

theorem tailTrace_1214108 : CollatzResearch.WordTrace tailWord_1214108 prefixEnd_1214108 623420970469041030566425 := by
  unfold tailWord_1214108
  simp only [CollatzResearch.WordTrace]
  refine ⟨22141078342750771991641489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29521437790334362655521985 22141078342750771991641489)
  ·
    refine ⟨16605808757063078993731117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22141078342750771991641489 16605808757063078993731117)
    ·
      refine ⟨6227178283898654622649169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16605808757063078993731117 6227178283898654622649169)
      ·
        refine ⟨4670383712923990966986877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6227178283898654622649169 4670383712923990966986877)
        ·
          refine ⟨1751393892346496612620079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4670383712923990966986877 1751393892346496612620079)
          ·
            refine ⟨2627090838519744918930119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751393892346496612620079 2627090838519744918930119)
            ·
              refine ⟨3940636257779617378395179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2627090838519744918930119 3940636257779617378395179)
              ·
                refine ⟨5910954386669426067592769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940636257779617378395179 5910954386669426067592769)
                ·
                  refine ⟨4433215790002069550694577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5910954386669426067592769 4433215790002069550694577)
                  ·
                    refine ⟨3324911842501552163020933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4433215790002069550694577 3324911842501552163020933)
                    ·
                      refine ⟨623420970469041030566425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3324911842501552163020933 623420970469041030566425)
                      ·
                        rfl

theorem cell23_1214108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1214108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214108 prefixEnd_1214108 := by exact prefixLift 1214108
  have htrace : WordTrace (prefixWord ++ tailWord_1214108) baseStart_1214108 baseEnd_1214108 := by
    simpa [prefixWord, tailWord_1214108, baseEnd_1214108] using wordTrace_append hprefix tailTrace_1214108
  have hstable : (prefixWord ++ tailWord_1214108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214108).length < 2 ^ (prefixWord ++ tailWord_1214108).sum := by decide
  have hdescent : baseEnd_1214108 < baseStart_1214108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214121 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 3, 7, 2]
def baseStart_1214121 : Nat := 118140960795 + 1214121 * 2 ^ 59
def prefixEnd_1214121 : Nat := 4983230072969 + 3 ^ 40 * 1214121 * 2
def baseEnd_1214121 : Nat := 623427645717549479703865

theorem tailTrace_1214121 : CollatzResearch.WordTrace tailWord_1214121 prefixEnd_1214121 623427645717549479703865 := by
  unfold tailWord_1214121
  simp only [CollatzResearch.WordTrace]
  refine ⟨44282630834454447203506217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29521753889636298135670811 44282630834454447203506217)
  ·
    refine ⟨33211973125840835402629663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44282630834454447203506217 33211973125840835402629663)
    ·
      refine ⟨49817959688761253103944495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33211973125840835402629663 49817959688761253103944495)
      ·
        refine ⟨74726939533141879655916743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49817959688761253103944495 74726939533141879655916743)
        ·
          refine ⟨112090409299712819483875115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74726939533141879655916743 112090409299712819483875115)
          ·
            refine ⟨168135613949569229225812673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112090409299712819483875115 168135613949569229225812673)
            ·
              refine ⟨126101710462176921919359505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168135613949569229225812673 126101710462176921919359505)
              ·
                refine ⟨94576282846632691439519629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126101710462176921919359505 94576282846632691439519629)
                ·
                  refine ⟨35466106067487259289819861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94576282846632691439519629 35466106067487259289819861)
                  ·
                    refine ⟨831236860956732639605153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35466106067487259289819861 831236860956732639605153)
                    ·
                      refine ⟨623427645717549479703865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831236860956732639605153 623427645717549479703865)
                      ·
                        rfl

theorem cell23_1214121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 7, 2].length) (baseStart_1214121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214121 prefixEnd_1214121 := by exact prefixLift 1214121
  have htrace : WordTrace (prefixWord ++ tailWord_1214121) baseStart_1214121 baseEnd_1214121 := by
    simpa [prefixWord, tailWord_1214121, baseEnd_1214121] using wordTrace_append hprefix tailTrace_1214121
  have hstable : (prefixWord ++ tailWord_1214121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214121).length < 2 ^ (prefixWord ++ tailWord_1214121).sum := by decide
  have hdescent : baseEnd_1214121 < baseStart_1214121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214124 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_1214124 : Nat := 118140960795 + 1214124 * 2 ^ 59
def prefixEnd_1214124 : Nat := 4983230072969 + 3 ^ 40 * 1214124 * 2
def baseEnd_1214124 : Nat := 623429186159512967966351

theorem tailTrace_1214124 : CollatzResearch.WordTrace tailWord_1214124 prefixEnd_1214124 623429186159512967966351 := by
  unfold tailWord_1214124
  simp only [CollatzResearch.WordTrace]
  refine ⟨22141370126721789357932713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29521826835629052477243617 22141370126721789357932713)
  ·
    refine ⟨16606027595041342018449535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22141370126721789357932713 16606027595041342018449535)
    ·
      refine ⟨24909041392562013027674303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16606027595041342018449535 24909041392562013027674303)
      ·
        refine ⟨37363562088843019541511455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24909041392562013027674303 37363562088843019541511455)
        ·
          refine ⟨56045343133264529312267183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37363562088843019541511455 56045343133264529312267183)
          ·
            refine ⟨84068014699896793968400775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56045343133264529312267183 84068014699896793968400775)
            ·
              refine ⟨126102022049845190952601163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84068014699896793968400775 126102022049845190952601163)
              ·
                refine ⟨189153033074767786428901745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126102022049845190952601163 189153033074767786428901745)
                ·
                  refine ⟨141864774806075839821676309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189153033074767786428901745 141864774806075839821676309)
                  ·
                    refine ⟨6649911319034804991641077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141864774806075839821676309 6649911319034804991641077)
                    ·
                      refine ⟨623429186159512967966351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6649911319034804991641077 623429186159512967966351)
                      ·
                        rfl

theorem cell23_1214124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_1214124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214124 prefixEnd_1214124 := by exact prefixLift 1214124
  have htrace : WordTrace (prefixWord ++ tailWord_1214124) baseStart_1214124 baseEnd_1214124 := by
    simpa [prefixWord, tailWord_1214124, baseEnd_1214124] using wordTrace_append hprefix tailTrace_1214124
  have hstable : (prefixWord ++ tailWord_1214124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214124).length < 2 ^ (prefixWord ++ tailWord_1214124).sum := by decide
  have hdescent : baseEnd_1214124 < baseStart_1214124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214146 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_1214146 : Nat := 118140960795 + 1214146 * 2 ^ 59
def prefixEnd_1214146 : Nat := 4983230072969 + 3 ^ 40 * 1214146 * 2
def baseEnd_1214146 : Nat := 623440482733911881891251

theorem tailTrace_1214146 : CollatzResearch.WordTrace tailWord_1214146 prefixEnd_1214146 623440482733911881891251 := by
  unfold tailWord_1214146
  simp only [CollatzResearch.WordTrace]
  refine ⟨11070885664840969118291573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29522361772909250982110861 11070885664840969118291573)
  ·
    refine ⟨1037895531078840854839835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11070885664840969118291573 1037895531078840854839835)
    ·
      refine ⟨1556843296618261282259753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037895531078840854839835 1556843296618261282259753)
      ·
        refine ⟨1167632472463695961694815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1556843296618261282259753 1167632472463695961694815)
        ·
          refine ⟨1751448708695543942542223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167632472463695961694815 1751448708695543942542223)
          ·
            refine ⟨2627173063043315913813335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751448708695543942542223 2627173063043315913813335)
            ·
              refine ⟨3940759594564973870720003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2627173063043315913813335 3940759594564973870720003)
              ·
                refine ⟨5911139391847460806080005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3940759594564973870720003 5911139391847460806080005)
                ·
                  refine ⟨1108338635971398901140001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5911139391847460806080005 1108338635971398901140001)
                  ·
                    refine ⟨831253976978549175855001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1108338635971398901140001 831253976978549175855001)
                    ·
                      refine ⟨623440482733911881891251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831253976978549175855001 623440482733911881891251)
                      ·
                        rfl

theorem cell23_1214146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_1214146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214146 prefixEnd_1214146 := by exact prefixLift 1214146
  have htrace : WordTrace (prefixWord ++ tailWord_1214146) baseStart_1214146 baseEnd_1214146 := by
    simpa [prefixWord, tailWord_1214146, baseEnd_1214146] using wordTrace_append hprefix tailTrace_1214146
  have hstable : (prefixWord ++ tailWord_1214146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214146).length < 2 ^ (prefixWord ++ tailWord_1214146).sum := by decide
  have hdescent : baseEnd_1214146 < baseStart_1214146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214151 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_1214151 : Nat := 118140960795 + 1214151 * 2 ^ 59
def prefixEnd_1214151 : Nat := 4983230072969 + 3 ^ 40 * 1214151 * 2
def baseEnd_1214151 : Nat := 623443050137184362328727

theorem tailTrace_1214151 : CollatzResearch.WordTrace tailWord_1214151 prefixEnd_1214151 623443050137184362328727 := by
  unfold tailWord_1214151
  simp only [CollatzResearch.WordTrace]
  refine ⟨44283725024345762327098307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29522483349563841551398871 44283725024345762327098307)
  ·
    refine ⟨66425587536518643490647461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44283725024345762327098307 66425587536518643490647461)
    ·
      refine ⟨12454797663097245654496399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66425587536518643490647461 12454797663097245654496399)
      ·
        refine ⟨18682196494645868481744599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12454797663097245654496399 18682196494645868481744599)
        ·
          refine ⟨28023294741968802722616899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18682196494645868481744599 28023294741968802722616899)
          ·
            refine ⟨42034942112953204083925349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28023294741968802722616899 42034942112953204083925349)
            ·
              refine ⟨7881551646178725765736003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42034942112953204083925349 7881551646178725765736003)
              ·
                refine ⟨11822327469268088648604005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7881551646178725765736003 11822327469268088648604005)
                ·
                  refine ⟨2216686400487766621613251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11822327469268088648604005 2216686400487766621613251)
                  ·
                    refine ⟨3325029600731649932419877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2216686400487766621613251 3325029600731649932419877)
                    ·
                      refine ⟨623443050137184362328727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3325029600731649932419877 623443050137184362328727)
                      ·
                        rfl

theorem cell23_1214151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_1214151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214151 prefixEnd_1214151 := by exact prefixLift 1214151
  have htrace : WordTrace (prefixWord ++ tailWord_1214151) baseStart_1214151 baseEnd_1214151 := by
    simpa [prefixWord, tailWord_1214151, baseEnd_1214151] using wordTrace_append hprefix tailTrace_1214151
  have hstable : (prefixWord ++ tailWord_1214151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214151).length < 2 ^ (prefixWord ++ tailWord_1214151).sum := by decide
  have hdescent : baseEnd_1214151 < baseStart_1214151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214168 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 2, 4, 2]
def baseStart_1214168 : Nat := 118140960795 + 1214168 * 2 ^ 59
def prefixEnd_1214168 : Nat := 4983230072969 + 3 ^ 40 * 1214168 * 2
def baseEnd_1214168 : Nat := 623451779308310795816149

theorem tailTrace_1214168 : CollatzResearch.WordTrace tailWord_1214168 prefixEnd_1214168 623451779308310795816149 := by
  unfold tailWord_1214168
  simp only [CollatzResearch.WordTrace]
  refine ⟨22142172532642087115233579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29522896710189449486978105 22142172532642087115233579)
  ·
    refine ⟨33213258798963130672850369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22142172532642087115233579 33213258798963130672850369)
    ·
      refine ⟨24909944099222348004637777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33213258798963130672850369 24909944099222348004637777)
      ·
        refine ⟨18682458074416761003478333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24909944099222348004637777 18682458074416761003478333)
        ·
          refine ⟨7005921777906285376304375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18682458074416761003478333 7005921777906285376304375)
          ·
            refine ⟨10508882666859428064456563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7005921777906285376304375 10508882666859428064456563)
            ·
              refine ⟨15763324000289142096684845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10508882666859428064456563 15763324000289142096684845)
              ·
                refine ⟨5911246500108428286256817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15763324000289142096684845 5911246500108428286256817)
                ·
                  refine ⟨4433434875081321214692613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5911246500108428286256817 4433434875081321214692613)
                  ·
                    refine ⟨831269039077747727754865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4433434875081321214692613 831269039077747727754865)
                    ·
                      refine ⟨623451779308310795816149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831269039077747727754865 623451779308310795816149)
                      ·
                        rfl

theorem cell23_1214168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_1214168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214168 prefixEnd_1214168 := by exact prefixLift 1214168
  have htrace : WordTrace (prefixWord ++ tailWord_1214168) baseStart_1214168 baseEnd_1214168 := by
    simpa [prefixWord, tailWord_1214168, baseEnd_1214168] using wordTrace_append hprefix tailTrace_1214168
  have hstable : (prefixWord ++ tailWord_1214168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214168).length < 2 ^ (prefixWord ++ tailWord_1214168).sum := by decide
  have hdescent : baseEnd_1214168 < baseStart_1214168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214181 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1214181 : Nat := 118140960795 + 1214181 * 2 ^ 59
def prefixEnd_1214181 : Nat := 4983230072969 + 3 ^ 40 * 1214181 * 2
def baseEnd_1214181 : Nat := 623458454556819244953589

theorem tailTrace_1214181 : CollatzResearch.WordTrace tailWord_1214181 prefixEnd_1214181 623458454556819244953589 := by
  unfold tailWord_1214181
  simp only [CollatzResearch.WordTrace]
  refine ⟨44284819214237077450690397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29523212809491384967126931 44284819214237077450690397)
  ·
    refine ⟨16606807205338904044008899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44284819214237077450690397 16606807205338904044008899)
    ·
      refine ⟨24910210808008356066013349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16606807205338904044008899 24910210808008356066013349)
      ·
        refine ⟨4670664526501566762377503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24910210808008356066013349 4670664526501566762377503)
        ·
          refine ⟨7005996789752350143566255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670664526501566762377503 7005996789752350143566255)
          ·
            refine ⟨10508995184628525215349383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7005996789752350143566255 10508995184628525215349383)
            ·
              refine ⟨15763492776942787823024075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10508995184628525215349383 15763492776942787823024075)
              ·
                refine ⟨23645239165414181734536113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15763492776942787823024075 23645239165414181734536113)
                ·
                  refine ⟨17733929374060636300902085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23645239165414181734536113 17733929374060636300902085)
                  ·
                    refine ⟨3325111757636369306419141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17733929374060636300902085 3325111757636369306419141)
                    ·
                      refine ⟨623458454556819244953589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3325111757636369306419141 623458454556819244953589)
                      ·
                        rfl

theorem cell23_1214181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1214181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214181 prefixEnd_1214181 := by exact prefixLift 1214181
  have htrace : WordTrace (prefixWord ++ tailWord_1214181) baseStart_1214181 baseEnd_1214181 := by
    simpa [prefixWord, tailWord_1214181, baseEnd_1214181] using wordTrace_append hprefix tailTrace_1214181
  have hstable : (prefixWord ++ tailWord_1214181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214181).length < 2 ^ (prefixWord ++ tailWord_1214181).sum := by decide
  have hdescent : baseEnd_1214181 < baseStart_1214181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214195 : List Nat := [1, 1, 1, 2, 2, 3, 5, 3, 1, 4]
def baseStart_1214195 : Nat := 118140960795 + 1214195 * 2 ^ 59
def prefixEnd_1214195 : Nat := 4983230072969 + 3 ^ 40 * 1214195 * 2
def baseEnd_1214195 : Nat := 207821881095327396726175

theorem tailTrace_1214195 : CollatzResearch.WordTrace tailWord_1214195 prefixEnd_1214195 207821881095327396726175 := by
  unfold tailWord_1214195
  simp only [CollatzResearch.WordTrace]
  refine ⟨44285329836186357841700039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29523553224124238561133359 44285329836186357841700039)
  ·
    refine ⟨66427994754279536762550059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44285329836186357841700039 66427994754279536762550059)
    ·
      refine ⟨99641992131419305143825089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66427994754279536762550059 99641992131419305143825089)
      ·
        refine ⟨74731494098564478857868817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99641992131419305143825089 74731494098564478857868817)
        ·
          refine ⟨56048620573923359143401613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74731494098564478857868817 56048620573923359143401613)
          ·
            refine ⟨21018232715221259678775605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56048620573923359143401613 21018232715221259678775605)
            ·
              refine ⟨1970459317051993094885213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21018232715221259678775605 1970459317051993094885213)
              ·
                refine ⟨738922243894497410581955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1970459317051993094885213 738922243894497410581955)
                ·
                  refine ⟨1108383365841746115872933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738922243894497410581955 1108383365841746115872933)
                  ·
                    refine ⟨207821881095327396726175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1108383365841746115872933 207821881095327396726175)
                    ·
                      rfl

theorem cell23_1214195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 4].length) (baseStart_1214195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214195 prefixEnd_1214195 := by exact prefixLift 1214195
  have htrace : WordTrace (prefixWord ++ tailWord_1214195) baseStart_1214195 baseEnd_1214195 := by
    simpa [prefixWord, tailWord_1214195, baseEnd_1214195] using wordTrace_append hprefix tailTrace_1214195
  have hstable : (prefixWord ++ tailWord_1214195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214195).length < 2 ^ (prefixWord ++ tailWord_1214195).sum := by decide
  have hdescent : baseEnd_1214195 < baseStart_1214195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214214 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1214214 : Nat := 118140960795 + 1214214 * 2 ^ 59
def prefixEnd_1214214 : Nat := 4983230072969 + 3 ^ 40 * 1214214 * 2
def baseEnd_1214214 : Nat := 623475399418417615840939

theorem tailTrace_1214214 : CollatzResearch.WordTrace tailWord_1214214 prefixEnd_1214214 623475399418417615840939 := by
  unfold tailWord_1214214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383938213222422627707553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29524015215411682724427797 1383938213222422627707553)
  ·
    refine ⟨1037953659916816970780665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1383938213222422627707553 1037953659916816970780665)
    ·
      refine ⟨778465244937612728085499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1037953659916816970780665 778465244937612728085499)
      ·
        refine ⟨1167697867406419092128249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778465244937612728085499 1167697867406419092128249)
        ·
          refine ⟨875773400554814319096187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1167697867406419092128249 875773400554814319096187)
          ·
            refine ⟨1313660100832221478644281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875773400554814319096187 1313660100832221478644281)
            ·
              refine ⟨985245075624166108983211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1313660100832221478644281 985245075624166108983211)
              ·
                refine ⟨1477867613436249163474817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985245075624166108983211 1477867613436249163474817)
                ·
                  refine ⟨1108400710077186872606113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1477867613436249163474817 1108400710077186872606113)
                  ·
                    refine ⟨831300532557890154454585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1108400710077186872606113 831300532557890154454585)
                    ·
                      refine ⟨623475399418417615840939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831300532557890154454585 623475399418417615840939)
                      ·
                        rfl

theorem cell23_1214214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1214214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214214 prefixEnd_1214214 := by exact prefixLift 1214214
  have htrace : WordTrace (prefixWord ++ tailWord_1214214) baseStart_1214214 baseEnd_1214214 := by
    simpa [prefixWord, tailWord_1214214, baseEnd_1214214] using wordTrace_append hprefix tailTrace_1214214
  have hstable : (prefixWord ++ tailWord_1214214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214214).length < 2 ^ (prefixWord ++ tailWord_1214214).sum := by decide
  have hdescent : baseEnd_1214214 < baseStart_1214214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214245 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 2, 3, 2]
def baseStart_1214245 : Nat := 118140960795 + 1214245 * 2 ^ 59
def prefixEnd_1214245 : Nat := 4983230072969 + 3 ^ 40 * 1214245 * 2
def baseEnd_1214245 : Nat := 623491317318706994553295

theorem tailTrace_1214245 : CollatzResearch.WordTrace tailWord_1214245 prefixEnd_1214245 623491317318706994553295 := by
  unfold tailWord_1214245
  simp only [CollatzResearch.WordTrace]
  refine ⟨44287153486005216381020189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29524768990670144254013459 44287153486005216381020189)
  ·
    refine ⟨16607682557251956142882571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44287153486005216381020189 16607682557251956142882571)
    ·
      refine ⟨24911523835877934214323857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16607682557251956142882571 24911523835877934214323857)
      ·
        refine ⟨18683642876908450660742893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24911523835877934214323857 18683642876908450660742893)
        ·
          refine ⟨7006366078840668997778585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18683642876908450660742893 7006366078840668997778585)
          ·
            refine ⟨5254774559130501748333939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7006366078840668997778585 5254774559130501748333939)
            ·
              refine ⟨7882161838695752622500909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254774559130501748333939 7882161838695752622500909)
              ·
                refine ⟨2955810689510907233437841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7882161838695752622500909 2955810689510907233437841)
                ·
                  refine ⟨2216858017133180425078381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2955810689510907233437841 2216858017133180425078381)
                  ·
                    refine ⟨831321756424942659404393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2216858017133180425078381 831321756424942659404393)
                    ·
                      refine ⟨623491317318706994553295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831321756424942659404393 623491317318706994553295)
                      ·
                        rfl

theorem cell23_1214245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_1214245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214245 prefixEnd_1214245 := by exact prefixLift 1214245
  have htrace : WordTrace (prefixWord ++ tailWord_1214245) baseStart_1214245 baseEnd_1214245 := by
    simpa [prefixWord, tailWord_1214245, baseEnd_1214245] using wordTrace_append hprefix tailTrace_1214245
  have hstable : (prefixWord ++ tailWord_1214245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214245).length < 2 ^ (prefixWord ++ tailWord_1214245).sum := by decide
  have hdescent : baseEnd_1214245 < baseStart_1214245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214268 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_1214268 : Nat := 118140960795 + 1214268 * 2 ^ 59
def prefixEnd_1214268 : Nat := 4983230072969 + 3 ^ 40 * 1214268 * 2
def baseEnd_1214268 : Nat := 207834375791253468188563

theorem tailTrace_1214268 : CollatzResearch.WordTrace tailWord_1214268 prefixEnd_1214268 207834375791253468188563 := by
  unfold tailWord_1214268
  simp only [CollatzResearch.WordTrace]
  refine ⟨22143996182460945654553729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29525328243281260872738305 22143996182460945654553729)
  ·
    refine ⟨16607997136845709240915297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22143996182460945654553729 16607997136845709240915297)
    ·
      refine ⟨12455997852634281930686473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16607997136845709240915297 12455997852634281930686473)
      ·
        refine ⟨9341998389475711448014855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12455997852634281930686473 9341998389475711448014855)
        ·
          refine ⟨14012997584213567172022283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9341998389475711448014855 14012997584213567172022283)
          ·
            refine ⟨21019496376320350758033425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14012997584213567172022283 21019496376320350758033425)
            ·
              refine ⟨15764622282240263068525069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21019496376320350758033425 15764622282240263068525069)
              ·
                refine ⟨5911733355840098650696901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15764622282240263068525069 5911733355840098650696901)
                ·
                  refine ⟨1108450004220018497005669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5911733355840098650696901 1108450004220018497005669)
                  ·
                    refine ⟨207834375791253468188563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1108450004220018497005669 207834375791253468188563)
                    ·
                      rfl

theorem cell23_1214268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_1214268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214268 prefixEnd_1214268 := by exact prefixLift 1214268
  have htrace : WordTrace (prefixWord ++ tailWord_1214268) baseStart_1214268 baseEnd_1214268 := by
    simpa [prefixWord, tailWord_1214268, baseEnd_1214268] using wordTrace_append hprefix tailTrace_1214268
  have hstable : (prefixWord ++ tailWord_1214268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214268).length < 2 ^ (prefixWord ++ tailWord_1214268).sum := by decide
  have hdescent : baseEnd_1214268 < baseStart_1214268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214269 : List Nat := [1, 4, 1, 4, 1, 2, 1, 4, 1, 1, 3]
def baseStart_1214269 : Nat := 118140960795 + 1214269 * 2 ^ 59
def prefixEnd_1214269 : Nat := 4983230072969 + 3 ^ 40 * 1214269 * 2
def baseEnd_1214269 : Nat := 623503640854414900653185

theorem tailTrace_1214269 : CollatzResearch.WordTrace tailWord_1214269 prefixEnd_1214269 623503640854414900653185 := by
  unfold tailWord_1214269
  simp only [CollatzResearch.WordTrace]
  refine ⟨44288028837918268479893861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29525352558612178986595907 44288028837918268479893861)
  ·
    refine ⟨8304005407109675339980099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44288028837918268479893861 8304005407109675339980099)
    ·
      refine ⟨12456008110664513009970149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8304005407109675339980099 12456008110664513009970149)
      ·
        refine ⟨2335501520749596189369403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12456008110664513009970149 2335501520749596189369403)
        ·
          refine ⟨3503252281124394284054105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335501520749596189369403 3503252281124394284054105)
          ·
            refine ⟨2627439210843295713040579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3503252281124394284054105 2627439210843295713040579)
            ·
              refine ⟨3941158816264943569560869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2627439210843295713040579 3941158816264943569560869)
              ·
                refine ⟨738967278049676919292663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3941158816264943569560869 738967278049676919292663)
                ·
                  refine ⟨1108450917074515378938995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 738967278049676919292663 1108450917074515378938995)
                  ·
                    refine ⟨1662676375611773068408493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1108450917074515378938995 1662676375611773068408493)
                    ·
                      refine ⟨623503640854414900653185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1662676375611773068408493 623503640854414900653185)
                      ·
                        rfl

theorem cell23_1214269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_1214269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214269 prefixEnd_1214269 := by exact prefixLift 1214269
  have htrace : WordTrace (prefixWord ++ tailWord_1214269) baseStart_1214269 baseEnd_1214269 := by
    simpa [prefixWord, tailWord_1214269, baseEnd_1214269] using wordTrace_append hprefix tailTrace_1214269
  have hstable : (prefixWord ++ tailWord_1214269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214269).length < 2 ^ (prefixWord ++ tailWord_1214269).sum := by decide
  have hdescent : baseEnd_1214269 < baseStart_1214269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214285 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1214285 : Nat := 118140960795 + 1214285 * 2 ^ 59
def prefixEnd_1214285 : Nat := 4983230072969 + 3 ^ 40 * 1214285 * 2
def baseEnd_1214285 : Nat := 207837285514962279351037

theorem tailTrace_1214285 : CollatzResearch.WordTrace tailWord_1214285 prefixEnd_1214285 207837285514962279351037 := by
  unfold tailWord_1214285
  simp only [CollatzResearch.WordTrace]
  refine ⟨44288612405860303212476309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29525741603906868808317539 44288612405860303212476309)
  ·
    refine ⟨2076028706524701713084827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44288612405860303212476309 2076028706524701713084827)
    ·
      refine ⟨3114043059787052569627241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2076028706524701713084827 3114043059787052569627241)
      ·
        refine ⟨2335532294840289427220431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3114043059787052569627241 2335532294840289427220431)
        ·
          refine ⟨3503298442260434140830647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2335532294840289427220431 3503298442260434140830647)
          ·
            refine ⟨5254947663390651211245971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3503298442260434140830647 5254947663390651211245971)
            ·
              refine ⟨7882421495085976816868957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254947663390651211245971 7882421495085976816868957)
              ·
                refine ⟨2955908060657241306325859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7882421495085976816868957 2955908060657241306325859)
                ·
                  refine ⟨4433862090985861959488789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2955908060657241306325859 4433862090985861959488789)
                  ·
                    refine ⟨207837285514962279351037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4433862090985861959488789 207837285514962279351037)
                    ·
                      rfl

theorem cell23_1214285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1214285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214285 prefixEnd_1214285 := by exact prefixLift 1214285
  have htrace : WordTrace (prefixWord ++ tailWord_1214285) baseStart_1214285 baseEnd_1214285 := by
    simpa [prefixWord, tailWord_1214285, baseEnd_1214285] using wordTrace_append hprefix tailTrace_1214285
  have hstable : (prefixWord ++ tailWord_1214285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214285).length < 2 ^ (prefixWord ++ tailWord_1214285).sum := by decide
  have hdescent : baseEnd_1214285 < baseStart_1214285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214292 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_1214292 : Nat := 118140960795 + 1214292 * 2 ^ 59
def prefixEnd_1214292 : Nat := 4983230072969 + 3 ^ 40 * 1214292 * 2
def baseEnd_1214292 : Nat := 623515450909468310665579

theorem tailTrace_1214292 : CollatzResearch.WordTrace tailWord_1214292 prefixEnd_1214292 623515450909468310665579 := by
  unfold tailWord_1214292
  simp only [CollatzResearch.WordTrace]
  refine ⟨22144433858417471703990565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29525911811223295605320753 22144433858417471703990565)
  ·
    refine ⟨4152081348453275944498231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22144433858417471703990565 4152081348453275944498231)
    ·
      refine ⟨6228122022679913916747347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4152081348453275944498231 6228122022679913916747347)
      ·
        refine ⟨9342183034019870875121021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6228122022679913916747347 9342183034019870875121021)
        ·
          refine ⟨3503318637757451578170383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9342183034019870875121021 3503318637757451578170383)
          ·
            refine ⟨5254977956636177367255575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3503318637757451578170383 5254977956636177367255575)
            ·
              refine ⟨7882466934954266050883363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254977956636177367255575 7882466934954266050883363)
              ·
                refine ⟨11823700402431399076325045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7882466934954266050883363 11823700402431399076325045)
                ·
                  refine ⟨1108471912727943663405473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11823700402431399076325045 1108471912727943663405473)
                  ·
                    refine ⟨831353934545957747554105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1108471912727943663405473 831353934545957747554105)
                    ·
                      refine ⟨623515450909468310665579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831353934545957747554105 623515450909468310665579)
                      ·
                        rfl

theorem cell23_1214292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_1214292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214292 prefixEnd_1214292 := by exact prefixLift 1214292
  have htrace : WordTrace (prefixWord ++ tailWord_1214292) baseStart_1214292 baseEnd_1214292 := by
    simpa [prefixWord, tailWord_1214292, baseEnd_1214292] using wordTrace_append hprefix tailTrace_1214292
  have hstable : (prefixWord ++ tailWord_1214292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214292).length < 2 ^ (prefixWord ++ tailWord_1214292).sum := by decide
  have hdescent : baseEnd_1214292 < baseStart_1214292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214298 : List Nat := [3, 1, 1, 2, 1, 3, 5, 7]
def baseStart_1214298 : Nat := 118140960795 + 1214298 * 2 ^ 59
def prefixEnd_1214298 : Nat := 4983230072969 + 3 ^ 40 * 1214298 * 2
def baseEnd_1214298 : Nat := 23093278955310936562613

theorem tailTrace_1214298 : CollatzResearch.WordTrace tailWord_1214298 prefixEnd_1214298 23093278955310936562613 := by
  unfold tailWord_1214298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11072271638703301608174887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29526057703208804288466365 11072271638703301608174887)
  ·
    refine ⟨16608407458054952412262331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11072271638703301608174887 16608407458054952412262331)
    ·
      refine ⟨24912611187082428618393497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16608407458054952412262331 24912611187082428618393497)
      ·
        refine ⟨18684458390311821463795123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24912611187082428618393497 18684458390311821463795123)
        ·
          refine ⟨28026687585467732195692685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18684458390311821463795123 28026687585467732195692685)
          ·
            refine ⟨10510007844550399573384757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28026687585467732195692685 10510007844550399573384757)
            ·
              refine ⟨985313235426599960004821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10510007844550399573384757 985313235426599960004821)
              ·
                refine ⟨23093278955310936562613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 985313235426599960004821 23093278955310936562613)
                ·
                  rfl

theorem cell23_1214298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 7].length) (baseStart_1214298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214298 prefixEnd_1214298 := by exact prefixLift 1214298
  have htrace : WordTrace (prefixWord ++ tailWord_1214298) baseStart_1214298 baseEnd_1214298 := by
    simpa [prefixWord, tailWord_1214298, baseEnd_1214298] using wordTrace_append hprefix tailTrace_1214298
  have hstable : (prefixWord ++ tailWord_1214298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214298).length < 2 ^ (prefixWord ++ tailWord_1214298).sum := by decide
  have hdescent : baseEnd_1214298 < baseStart_1214298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214326 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_1214326 : Nat := 118140960795 + 1214326 * 2 ^ 59
def prefixEnd_1214326 : Nat := 4983230072969 + 3 ^ 40 * 1214326 * 2
def baseEnd_1214326 : Nat := 623532909251721177640423

theorem tailTrace_1214326 : CollatzResearch.WordTrace tailWord_1214326 prefixEnd_1214326 623532909251721177640423 := by
  unfold tailWord_1214326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768131737419485450919927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29526738532474511476479221 2768131737419485450919927)
  ·
    refine ⟨4152197606129228176379891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2768131737419485450919927 4152197606129228176379891)
    ·
      refine ⟨6228296409193842264569837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4152197606129228176379891 6228296409193842264569837)
      ·
        refine ⟨2335611153447690849213689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6228296409193842264569837 2335611153447690849213689)
        ·
          refine ⟨1751708365085768136910267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2335611153447690849213689 1751708365085768136910267)
          ·
            refine ⟨2627562547628652205365401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751708365085768136910267 2627562547628652205365401)
            ·
              refine ⟨1970671910721489154024051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2627562547628652205365401 1970671910721489154024051)
              ·
                refine ⟨2956007866082233731036077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970671910721489154024051 2956007866082233731036077)
                ·
                  refine ⟨1108502949780837649138529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2956007866082233731036077 1108502949780837649138529)
                  ·
                    refine ⟨831377212335628236853897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1108502949780837649138529 831377212335628236853897)
                    ·
                      refine ⟨623532909251721177640423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831377212335628236853897 623532909251721177640423)
                      ·
                        rfl

theorem cell23_1214326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_1214326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214326 prefixEnd_1214326 := by exact prefixLift 1214326
  have htrace : WordTrace (prefixWord ++ tailWord_1214326) baseStart_1214326 baseEnd_1214326 := by
    simpa [prefixWord, tailWord_1214326, baseEnd_1214326] using wordTrace_append hprefix tailTrace_1214326
  have hstable : (prefixWord ++ tailWord_1214326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214326).length < 2 ^ (prefixWord ++ tailWord_1214326).sum := by decide
  have hdescent : baseEnd_1214326 < baseStart_1214326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214360 : List Nat := [2, 1, 2, 6, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1214360 : Nat := 118140960795 + 1214360 * 2 ^ 59
def prefixEnd_1214360 : Nat := 4983230072969 + 3 ^ 40 * 1214360 * 2
def baseEnd_1214360 : Nat := 623550367593974044615267

theorem tailTrace_1214360 : CollatzResearch.WordTrace tailWord_1214360 prefixEnd_1214360 623550367593974044615267 := by
  unfold tailWord_1214360
  simp only [CollatzResearch.WordTrace]
  refine ⟨22145673940294295510728267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29527565253725727347637689 22145673940294295510728267)
  ·
    refine ⟨33218510910441443266092401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22145673940294295510728267 33218510910441443266092401)
    ·
      refine ⟨24913883182831082449569301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33218510910441443266092401 24913883182831082449569301)
      ·
        refine ⟨1167838274195206989823561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24913883182831082449569301 1167838274195206989823561)
        ·
          refine ⟨875878705646405242367671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1167838274195206989823561 875878705646405242367671)
          ·
            refine ⟨1313818058469607863551507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875878705646405242367671 1313818058469607863551507)
            ·
              refine ⟨1970727087704411795327261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313818058469607863551507 1970727087704411795327261)
              ·
                refine ⟨739022657889154423247723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1970727087704411795327261 739022657889154423247723)
                ·
                  refine ⟨1108533986833731634871585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739022657889154423247723 1108533986833731634871585)
                  ·
                    refine ⟨831400490125298726153689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1108533986833731634871585 831400490125298726153689)
                    ·
                      refine ⟨623550367593974044615267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831400490125298726153689 623550367593974044615267)
                      ·
                        rfl

theorem cell23_1214360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1214360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214360 prefixEnd_1214360 := by exact prefixLift 1214360
  have htrace : WordTrace (prefixWord ++ tailWord_1214360) baseStart_1214360 baseEnd_1214360 := by
    simpa [prefixWord, tailWord_1214360, baseEnd_1214360] using wordTrace_append hprefix tailTrace_1214360
  have hstable : (prefixWord ++ tailWord_1214360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214360).length < 2 ^ (prefixWord ++ tailWord_1214360).sum := by decide
  have hdescent : baseEnd_1214360 < baseStart_1214360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214368 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 3]
def baseStart_1214368 : Nat := 118140960795 + 1214368 * 2 ^ 59
def prefixEnd_1214368 : Nat := 4983230072969 + 3 ^ 40 * 1214368 * 2
def baseEnd_1214368 : Nat := 623554475439210013315229

theorem tailTrace_1214368 : CollatzResearch.WordTrace tailWord_1214368 prefixEnd_1214368 623554475439210013315229 := by
  unfold tailWord_1214368
  simp only [CollatzResearch.WordTrace]
  refine ⟨22145819832279804193873879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29527759776373072258498505 22145819832279804193873879)
  ·
    refine ⟨33218729748419706290810819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22145819832279804193873879 33218729748419706290810819)
    ·
      refine ⟨49828094622629559436216229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33218729748419706290810819 49828094622629559436216229)
      ·
        refine ⟨9342767741743042394290543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49828094622629559436216229 9342767741743042394290543)
        ·
          refine ⟨14014151612614563591435815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9342767741743042394290543 14014151612614563591435815)
          ·
            refine ⟨21021227418921845387153723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14014151612614563591435815 21021227418921845387153723)
            ·
              refine ⟨31531841128382768080730585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21021227418921845387153723 31531841128382768080730585)
              ·
                refine ⟨23648880846287076060547939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31531841128382768080730585 23648880846287076060547939)
                ·
                  refine ⟨35473321269430614090821909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23648880846287076060547939 35473321269430614090821909)
                  ·
                    refine ⟨1662811934504560035507277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35473321269430614090821909 1662811934504560035507277)
                    ·
                      refine ⟨623554475439210013315229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1662811934504560035507277 623554475439210013315229)
                      ·
                        rfl

theorem cell23_1214368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_1214368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214368 prefixEnd_1214368 := by exact prefixLift 1214368
  have htrace : WordTrace (prefixWord ++ tailWord_1214368) baseStart_1214368 baseEnd_1214368 := by
    simpa [prefixWord, tailWord_1214368, baseEnd_1214368] using wordTrace_append hprefix tailTrace_1214368
  have hstable : (prefixWord ++ tailWord_1214368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214368).length < 2 ^ (prefixWord ++ tailWord_1214368).sum := by decide
  have hdescent : baseEnd_1214368 < baseStart_1214368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214435 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 2, 5]
def baseStart_1214435 : Nat := 118140960795 + 1214435 * 2 ^ 59
def prefixEnd_1214435 : Nat := 4983230072969 + 3 ^ 40 * 1214435 * 2
def baseEnd_1214435 : Nat := 207862959547687083725807

theorem tailTrace_1214435 : CollatzResearch.WordTrace tailWord_1214435 prefixEnd_1214435 207862959547687083725807 := by
  unfold tailWord_1214435
  simp only [CollatzResearch.WordTrace]
  refine ⟨44294083355316878830436759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29529388903544585886957839 44294083355316878830436759)
  ·
    refine ⟨66441125032975318245655139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44294083355316878830436759 66441125032975318245655139)
    ·
      refine ⟨99661687549462977368482709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66441125032975318245655139 99661687549462977368482709)
      ·
        refine ⟨4671641603881077064147627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99661687549462977368482709 4671641603881077064147627)
        ·
          refine ⟨7007462405821615596221441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4671641603881077064147627 7007462405821615596221441)
          ·
            refine ⟨5255596804366211697166081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7007462405821615596221441 5255596804366211697166081)
            ·
              refine ⟨3941697603274658772874561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5255596804366211697166081 3941697603274658772874561)
              ·
                refine ⟨2956273202455994079655921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3941697603274658772874561 2956273202455994079655921)
                ·
                  refine ⟨2217204901841995559741941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2956273202455994079655921 2217204901841995559741941)
                  ·
                    refine ⟨207862959547687083725807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2217204901841995559741941 207862959547687083725807)
                    ·
                      rfl

theorem cell23_1214435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 5].length) (baseStart_1214435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214435 prefixEnd_1214435 := by exact prefixLift 1214435
  have htrace : WordTrace (prefixWord ++ tailWord_1214435) baseStart_1214435 baseEnd_1214435 := by
    simpa [prefixWord, tailWord_1214435, baseEnd_1214435] using wordTrace_append hprefix tailTrace_1214435
  have hstable : (prefixWord ++ tailWord_1214435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214435).length < 2 ^ (prefixWord ++ tailWord_1214435).sum := by decide
  have hdescent : baseEnd_1214435 < baseStart_1214435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214475 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 3]
def baseStart_1214475 : Nat := 118140960795 + 1214475 * 2 ^ 59
def prefixEnd_1214475 : Nat := 4983230072969 + 3 ^ 40 * 1214475 * 2
def baseEnd_1214475 : Nat := 623609417869241094677237

theorem tailTrace_1214475 : CollatzResearch.WordTrace tailWord_1214475 prefixEnd_1214475 623609417869241094677237 := by
  unfold tailWord_1214475
  simp only [CollatzResearch.WordTrace]
  refine ⟨44295542275171965661892879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29530361516781310441261919 44295542275171965661892879)
  ·
    refine ⟨66443313412757948492839319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44295542275171965661892879 66443313412757948492839319)
    ·
      refine ⟨99664970119136922739258979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66443313412757948492839319 99664970119136922739258979)
      ·
        refine ⟨149497455178705384108888469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99664970119136922739258979 149497455178705384108888469)
        ·
          refine ⟨7007693211501814880104147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 149497455178705384108888469 7007693211501814880104147)
          ·
            refine ⟨10511539817252722320156221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7007693211501814880104147 10511539817252722320156221)
            ·
              refine ⟨3941827431469770870058583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10511539817252722320156221 3941827431469770870058583)
              ·
                refine ⟨5912741147204656305087875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3941827431469770870058583 5912741147204656305087875)
                ·
                  refine ⟨8869111720806984457631813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5912741147204656305087875 8869111720806984457631813)
                  ·
                    refine ⟨1662958447651309585805965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8869111720806984457631813 1662958447651309585805965)
                    ·
                      refine ⟨623609417869241094677237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1662958447651309585805965 623609417869241094677237)
                      ·
                        rfl

theorem cell23_1214475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 3].length) (baseStart_1214475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214475 prefixEnd_1214475 := by exact prefixLift 1214475
  have htrace : WordTrace (prefixWord ++ tailWord_1214475) baseStart_1214475 baseEnd_1214475 := by
    simpa [prefixWord, tailWord_1214475, baseEnd_1214475] using wordTrace_append hprefix tailTrace_1214475
  have hstable : (prefixWord ++ tailWord_1214475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214475).length < 2 ^ (prefixWord ++ tailWord_1214475).sum := by decide
  have hdescent : baseEnd_1214475 < baseStart_1214475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214508 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_1214508 : Nat := 118140960795 + 1214508 * 2 ^ 59
def prefixEnd_1214508 : Nat := 4983230072969 + 3 ^ 40 * 1214508 * 2
def baseEnd_1214508 : Nat := 207875454243613155188195

theorem tailTrace_1214508 : CollatzResearch.WordTrace tailWord_1214508 prefixEnd_1214508 207875454243613155188195 := by
  unfold tailWord_1214508
  simp only [CollatzResearch.WordTrace]
  refine ⟨22148372942026206148922089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29531163922701608198562785 22148372942026206148922089)
  ·
    refine ⟨16611279706519654611691567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22148372942026206148922089 16611279706519654611691567)
    ·
      refine ⟨24916919559779481917537351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16611279706519654611691567 24916919559779481917537351)
      ·
        refine ⟨37375379339669222876306027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24916919559779481917537351 37375379339669222876306027)
        ·
          refine ⟨56063069009503834314459041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37375379339669222876306027 56063069009503834314459041)
          ·
            refine ⟨42047301757127875735844281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56063069009503834314459041 42047301757127875735844281)
            ·
              refine ⟨31535476317845906801883211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42047301757127875735844281 31535476317845906801883211)
              ·
                refine ⟨47303214476768860202824817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31535476317845906801883211 47303214476768860202824817)
                ·
                  refine ⟨35477410857576645152118613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47303214476768860202824817 35477410857576645152118613)
                  ·
                    refine ⟨207875454243613155188195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 35477410857576645152118613 207875454243613155188195)
                    ·
                      rfl

theorem cell23_1214508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_1214508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214508 prefixEnd_1214508 := by exact prefixLift 1214508
  have htrace : WordTrace (prefixWord ++ tailWord_1214508) baseStart_1214508 baseEnd_1214508 := by
    simpa [prefixWord, tailWord_1214508, baseEnd_1214508] using wordTrace_append hprefix tailTrace_1214508
  have hstable : (prefixWord ++ tailWord_1214508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214508).length < 2 ^ (prefixWord ++ tailWord_1214508).sum := by decide
  have hdescent : baseEnd_1214508 < baseStart_1214508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214512 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 6]
def baseStart_1214512 : Nat := 118140960795 + 1214512 * 2 ^ 59
def prefixEnd_1214512 : Nat := 4983230072969 + 3 ^ 40 * 1214512 * 2
def baseEnd_1214512 : Nat := 69292046294828605546063

theorem tailTrace_1214512 : CollatzResearch.WordTrace tailWord_1214512 prefixEnd_1214512 69292046294828605546063 := by
  unfold tailWord_1214512
  simp only [CollatzResearch.WordTrace]
  refine ⟨22148445888018960490494895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29531261184025280653993193 22148445888018960490494895)
  ·
    refine ⟨33222668832028440735742343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22148445888018960490494895 33222668832028440735742343)
    ·
      refine ⟨49834003248042661103613515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33222668832028440735742343 49834003248042661103613515)
      ·
        refine ⟨74751004872063991655420273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49834003248042661103613515 74751004872063991655420273)
        ·
          refine ⟨56063253654047993741565205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74751004872063991655420273 56063253654047993741565205)
          ·
            refine ⟨2627965015033499706635869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56063253654047993741565205 2627965015033499706635869)
            ·
              refine ⟨985486880637562389988451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2627965015033499706635869 985486880637562389988451)
              ·
                refine ⟨1478230320956343584982677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985486880637562389988451 1478230320956343584982677)
                ·
                  refine ⟨69292046294828605546063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1478230320956343584982677 69292046294828605546063)
                  ·
                    rfl

theorem cell23_1214512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 6].length) (baseStart_1214512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214512 prefixEnd_1214512 := by exact prefixLift 1214512
  have htrace : WordTrace (prefixWord ++ tailWord_1214512) baseStart_1214512 baseEnd_1214512 := by
    simpa [prefixWord, tailWord_1214512, baseEnd_1214512] using wordTrace_append hprefix tailTrace_1214512
  have hstable : (prefixWord ++ tailWord_1214512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214512).length < 2 ^ (prefixWord ++ tailWord_1214512).sum := by decide
  have hdescent : baseEnd_1214512 < baseStart_1214512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214542 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_1214542 : Nat := 118140960795 + 1214542 * 2 ^ 59
def prefixEnd_1214542 : Nat := 4983230072969 + 3 ^ 40 * 1214542 * 2
def baseEnd_1214542 : Nat := 207881273691030777513143

theorem tailTrace_1214542 : CollatzResearch.WordTrace tailWord_1214542 prefixEnd_1214542 207881273691030777513143 := by
  unfold tailWord_1214542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537248245741154513072735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29531990643952824069721253 5537248245741154513072735)
  ·
    refine ⟨8305872368611731769609103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5537248245741154513072735 8305872368611731769609103)
    ·
      refine ⟨12458808552917597654413655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8305872368611731769609103 12458808552917597654413655)
      ·
        refine ⟨18688212829376396481620483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12458808552917597654413655 18688212829376396481620483)
        ·
          refine ⟨28032319244064594722430725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18688212829376396481620483 28032319244064594722430725)
          ·
            refine ⟨5256059858262111510455761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28032319244064594722430725 5256059858262111510455761)
            ·
              refine ⟨3942044893696583632841821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5256059858262111510455761 3942044893696583632841821)
              ·
                refine ⟨1478266835136218862315683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3942044893696583632841821 1478266835136218862315683)
                ·
                  refine ⟨2217400252704328293473525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478266835136218862315683 2217400252704328293473525)
                  ·
                    refine ⟨207881273691030777513143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2217400252704328293473525 207881273691030777513143)
                    ·
                      rfl

theorem cell23_1214542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_1214542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214542 prefixEnd_1214542 := by exact prefixLift 1214542
  have htrace : WordTrace (prefixWord ++ tailWord_1214542) baseStart_1214542 baseEnd_1214542 := by
    simpa [prefixWord, tailWord_1214542, baseEnd_1214542] using wordTrace_append hprefix tailTrace_1214542
  have hstable : (prefixWord ++ tailWord_1214542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214542).length < 2 ^ (prefixWord ++ tailWord_1214542).sum := by decide
  have hdescent : baseEnd_1214542 < baseStart_1214542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214545 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_1214545 : Nat := 118140960795 + 1214545 * 2 ^ 59
def prefixEnd_1214545 : Nat := 4983230072969 + 3 ^ 40 * 1214545 * 2
def baseEnd_1214545 : Nat := 623645361515055820801915

theorem tailTrace_1214545 : CollatzResearch.WordTrace tailWord_1214545 prefixEnd_1214545 623645361515055820801915 := by
  unfold tailWord_1214545
  simp only [CollatzResearch.WordTrace]
  refine ⟨44298095384918367616941089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29532063589945578411294059 44298095384918367616941089)
  ·
    refine ⟨33223571538688775712705817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44298095384918367616941089 33223571538688775712705817)
    ·
      refine ⟨24917678654016581784529363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33223571538688775712705817 24917678654016581784529363)
      ·
        refine ⟨37376517981024872676794045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24917678654016581784529363 37376517981024872676794045)
        ·
          refine ⟨14016194242884327253797767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37376517981024872676794045 14016194242884327253797767)
          ·
            refine ⟨21024291364326490880696651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14016194242884327253797767 21024291364326490880696651)
            ·
              refine ⟨31536437046489736321044977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21024291364326490880696651 31536437046489736321044977)
              ·
                refine ⟨23652327784867302240783733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31536437046489736321044977 23652327784867302240783733)
                ·
                  refine ⟨2217405729831309585073475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23652327784867302240783733 2217405729831309585073475)
                  ·
                    refine ⟨3326108594746964377610213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2217405729831309585073475 3326108594746964377610213)
                    ·
                      refine ⟨623645361515055820801915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3326108594746964377610213 623645361515055820801915)
                      ·
                        rfl

theorem cell23_1214545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_1214545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214545 prefixEnd_1214545 := by exact prefixLift 1214545
  have htrace : WordTrace (prefixWord ++ tailWord_1214545) baseStart_1214545 baseEnd_1214545 := by
    simpa [prefixWord, tailWord_1214545, baseEnd_1214545] using wordTrace_append hprefix tailTrace_1214545
  have hstable : (prefixWord ++ tailWord_1214545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214545).length < 2 ^ (prefixWord ++ tailWord_1214545).sum := by decide
  have hdescent : baseEnd_1214545 < baseStart_1214545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214549 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_1214549 : Nat := 118140960795 + 1214549 * 2 ^ 59
def prefixEnd_1214549 : Nat := 4983230072969 + 3 ^ 40 * 1214549 * 2
def baseEnd_1214549 : Nat := 623647415437673805151897

theorem tailTrace_1214549 : CollatzResearch.WordTrace tailWord_1214549 prefixEnd_1214549 623647415437673805151897 := by
  unfold tailWord_1214549
  simp only [CollatzResearch.WordTrace]
  refine ⟨44298241276903876300086701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29532160851269250866724467 44298241276903876300086701)
  ·
    refine ⟨16611840478838953612532513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44298241276903876300086701 16611840478838953612532513)
    ·
      refine ⟨12458880359129215209399385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16611840478838953612532513 12458880359129215209399385)
      ·
        refine ⟨9344160269346911407049539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12458880359129215209399385 9344160269346911407049539)
        ·
          refine ⟨14016240404020367110574309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9344160269346911407049539 14016240404020367110574309)
          ·
            refine ⟨2628045075753818833232683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14016240404020367110574309 2628045075753818833232683)
            ·
              refine ⟨3942067613630728249849025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628045075753818833232683 3942067613630728249849025)
              ·
                refine ⟨2956550710223046187386769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3942067613630728249849025 2956550710223046187386769)
                ·
                  refine ⟨2217413032667284640540077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2956550710223046187386769 2217413032667284640540077)
                  ·
                    refine ⟨831529887250231740202529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2217413032667284640540077 831529887250231740202529)
                    ·
                      refine ⟨623647415437673805151897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831529887250231740202529 623647415437673805151897)
                      ·
                        rfl

theorem cell23_1214549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_1214549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214549 prefixEnd_1214549 := by exact prefixLift 1214549
  have htrace : WordTrace (prefixWord ++ tailWord_1214549) baseStart_1214549 baseEnd_1214549 := by
    simpa [prefixWord, tailWord_1214549, baseEnd_1214549] using wordTrace_append hprefix tailTrace_1214549
  have hstable : (prefixWord ++ tailWord_1214549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214549).length < 2 ^ (prefixWord ++ tailWord_1214549).sum := by decide
  have hdescent : baseEnd_1214549 < baseStart_1214549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214550 : List Nat := [5, 2, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1214550 : Nat := 118140960795 + 1214550 * 2 ^ 59
def prefixEnd_1214550 : Nat := 4983230072969 + 3 ^ 40 * 1214550 * 2
def baseEnd_1214550 : Nat := 207882642972776100413131

theorem tailTrace_1214550 : CollatzResearch.WordTrace tailWord_1214550 prefixEnd_1214550 207882642972776100413131 := by
  unfold tailWord_1214550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768642359368765841929569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29532185166600168980582069 2768642359368765841929569)
  ·
    refine ⟨2076481769526574381447177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2768642359368765841929569 2076481769526574381447177)
    ·
      refine ⟨1557361327144930786085383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2076481769526574381447177 1557361327144930786085383)
      ·
        refine ⟨2336041990717396179128075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557361327144930786085383 2336041990717396179128075)
        ·
          refine ⟨3504062986076094268692113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336041990717396179128075 3504062986076094268692113)
          ·
            refine ⟨2628047239557070701519085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3504062986076094268692113 2628047239557070701519085)
            ·
              refine ⟨985517714833901513069657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2628047239557070701519085 985517714833901513069657)
              ·
                refine ⟨739138286125426134802243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985517714833901513069657 739138286125426134802243)
                ·
                  refine ⟨1108707429188139202203365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739138286125426134802243 1108707429188139202203365)
                  ·
                    refine ⟨207882642972776100413131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1108707429188139202203365 207882642972776100413131)
                    ·
                      rfl

theorem cell23_1214550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1214550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214550 prefixEnd_1214550 := by exact prefixLift 1214550
  have htrace : WordTrace (prefixWord ++ tailWord_1214550) baseStart_1214550 baseEnd_1214550 := by
    simpa [prefixWord, tailWord_1214550, baseEnd_1214550] using wordTrace_append hprefix tailTrace_1214550
  have hstable : (prefixWord ++ tailWord_1214550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214550).length < 2 ^ (prefixWord ++ tailWord_1214550).sum := by decide
  have hdescent : baseEnd_1214550 < baseStart_1214550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214556 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_1214556 : Nat := 118140960795 + 1214556 * 2 ^ 59
def prefixEnd_1214556 : Nat := 4983230072969 + 3 ^ 40 * 1214556 * 2
def baseEnd_1214556 : Nat := 623651009802255277764365

theorem tailTrace_1214556 : CollatzResearch.WordTrace tailWord_1214556 prefixEnd_1214556 623651009802255277764365 := by
  unfold tailWord_1214556
  simp only [CollatzResearch.WordTrace]
  refine ⟨22149248293939258247795761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29532331058585677663727681 22149248293939258247795761)
  ·
    refine ⟨16611936220454443685846821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22149248293939258247795761 16611936220454443685846821)
    ·
      refine ⟨3114738041335208191096279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16611936220454443685846821 3114738041335208191096279)
      ·
        refine ⟨4672107062002812286644419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3114738041335208191096279 4672107062002812286644419)
        ·
          refine ⟨7008160593004218429966629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4672107062002812286644419 7008160593004218429966629)
          ·
            refine ⟨1314030111188290955618743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7008160593004218429966629 1314030111188290955618743)
            ·
              refine ⟨1971045166782436433428115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314030111188290955618743 1971045166782436433428115)
              ·
                refine ⟨2956567750173654650142173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971045166782436433428115 2956567750173654650142173)
                ·
                  refine ⟨1108712906315120493803315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2956567750173654650142173 1108712906315120493803315)
                  ·
                    refine ⟨1663069359472680740704973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1108712906315120493803315 1663069359472680740704973)
                    ·
                      refine ⟨623651009802255277764365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1663069359472680740704973 623651009802255277764365)
                      ·
                        rfl

theorem cell23_1214556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_1214556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214556 prefixEnd_1214556 := by exact prefixLift 1214556
  have htrace : WordTrace (prefixWord ++ tailWord_1214556) baseStart_1214556 baseEnd_1214556 := by
    simpa [prefixWord, tailWord_1214556, baseEnd_1214556] using wordTrace_append hprefix tailTrace_1214556
  have hstable : (prefixWord ++ tailWord_1214556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214556).length < 2 ^ (prefixWord ++ tailWord_1214556).sum := by decide
  have hdescent : baseEnd_1214556 < baseStart_1214556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214575 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_1214575 : Nat := 118140960795 + 1214575 * 2 ^ 59
def prefixEnd_1214575 : Nat := 4983230072969 + 3 ^ 40 * 1214575 * 2
def baseEnd_1214575 : Nat := 623660765934690703426777

theorem tailTrace_1214575 : CollatzResearch.WordTrace tailWord_1214575 prefixEnd_1214575 623660765934690703426777 := by
  unfold tailWord_1214575
  simp only [CollatzResearch.WordTrace]
  refine ⟨44299189574809682740533179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29532793049873121827022119 44299189574809682740533179)
  ·
    refine ⟨66448784362214524110799769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44299189574809682740533179 66448784362214524110799769)
    ·
      refine ⟨49836588271660893083099827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66448784362214524110799769 49836588271660893083099827)
      ·
        refine ⟨74754882407491339624649741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49836588271660893083099827 74754882407491339624649741)
        ·
          refine ⟨28033080902809252359243653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74754882407491339624649741 28033080902809252359243653)
          ·
            refine ⟨5256202669276734817358185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28033080902809252359243653 5256202669276734817358185)
            ·
              refine ⟨3942152001957551113018639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5256202669276734817358185 3942152001957551113018639)
              ·
                refine ⟨5913228002936326669527959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3942152001957551113018639 5913228002936326669527959)
                ·
                  refine ⟨8869842004404490004291939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5913228002936326669527959 8869842004404490004291939)
                  ·
                    refine ⟨13304763006606735006437909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8869842004404490004291939 13304763006606735006437909)
                    ·
                      refine ⟨623660765934690703426777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13304763006606735006437909 623660765934690703426777)
                      ·
                        rfl

theorem cell23_1214575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_1214575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214575 prefixEnd_1214575 := by exact prefixLift 1214575
  have htrace : WordTrace (prefixWord ++ tailWord_1214575) baseStart_1214575 baseEnd_1214575 := by
    simpa [prefixWord, tailWord_1214575, baseEnd_1214575] using wordTrace_append hprefix tailTrace_1214575
  have hstable : (prefixWord ++ tailWord_1214575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214575).length < 2 ^ (prefixWord ++ tailWord_1214575).sum := by decide
  have hdescent : baseEnd_1214575 < baseStart_1214575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214585 : List Nat := [1, 2, 1, 3, 4, 1, 2, 9]
def baseStart_1214585 : Nat := 118140960795 + 1214585 * 2 ^ 59
def prefixEnd_1214585 : Nat := 4983230072969 + 3 ^ 40 * 1214585 * 2
def baseEnd_1214585 : Nat := 23098737064490209788953

theorem tailTrace_1214585 : CollatzResearch.WordTrace tailWord_1214585 prefixEnd_1214585 23098737064490209788953 := by
  unfold tailWord_1214585
  simp only [CollatzResearch.WordTrace]
  refine ⟨44299554304773454448397209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29533036203182302965598139 44299554304773454448397209)
  ·
    refine ⟨33224665728580090836297907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44299554304773454448397209 33224665728580090836297907)
    ·
      refine ⟨49836998592870136254446861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33224665728580090836297907 49836998592870136254446861)
      ·
        refine ⟨18688874472326301095417573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49836998592870136254446861 18688874472326301095417573)
        ·
          refine ⟨3504163963561181455390795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18688874472326301095417573 3504163963561181455390795)
          ·
            refine ⟨5256245945341772183086193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504163963561181455390795 5256245945341772183086193)
            ·
              refine ⟨3942184459006329137314645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5256245945341772183086193 3942184459006329137314645)
              ·
                refine ⟨23098737064490209788953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3942184459006329137314645 23098737064490209788953)
                ·
                  rfl

theorem cell23_1214585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 9].length) (baseStart_1214585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214585 prefixEnd_1214585 := by exact prefixLift 1214585
  have htrace : WordTrace (prefixWord ++ tailWord_1214585) baseStart_1214585 baseEnd_1214585 := by
    simpa [prefixWord, tailWord_1214585, baseEnd_1214585] using wordTrace_append hprefix tailTrace_1214585
  have hstable : (prefixWord ++ tailWord_1214585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214585).length < 2 ^ (prefixWord ++ tailWord_1214585).sum := by decide
  have hdescent : baseEnd_1214585 < baseStart_1214585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214606 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 2, 4]
def baseStart_1214606 : Nat := 118140960795 + 1214606 * 2 ^ 59
def prefixEnd_1214606 : Nat := 4983230072969 + 3 ^ 40 * 1214606 * 2
def baseEnd_1214606 : Nat := 207892227944993360713045

theorem tailTrace_1214606 : CollatzResearch.WordTrace tailWord_1214606 prefixEnd_1214606 207892227944993360713045 := by
  unfold tailWord_1214606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5537540029712171879363959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29533546825131583356607781 5537540029712171879363959)
  ·
    refine ⟨8306310044568257819045939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5537540029712171879363959 8306310044568257819045939)
    ·
      refine ⟨12459465066852386728568909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8306310044568257819045939 12459465066852386728568909)
      ·
        refine ⟨4672299400069645023213341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12459465066852386728568909 4672299400069645023213341)
        ·
          refine ⟨1752112275026116883705003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4672299400069645023213341 1752112275026116883705003)
          ·
            refine ⟨2628168412539175325557505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752112275026116883705003 2628168412539175325557505)
            ·
              refine ⟨1971126309404381494168129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2628168412539175325557505 1971126309404381494168129)
              ·
                refine ⟨1478344732053286120626097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1971126309404381494168129 1478344732053286120626097)
                ·
                  refine ⟨1108758549039964590469573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1478344732053286120626097 1108758549039964590469573)
                  ·
                    refine ⟨207892227944993360713045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1108758549039964590469573 207892227944993360713045)
                    ·
                      rfl

theorem cell23_1214606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_1214606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214606 prefixEnd_1214606 := by exact prefixLift 1214606
  have htrace : WordTrace (prefixWord ++ tailWord_1214606) baseStart_1214606 baseEnd_1214606 := by
    simpa [prefixWord, tailWord_1214606, baseEnd_1214606] using wordTrace_append hprefix tailTrace_1214606
  have hstable : (prefixWord ++ tailWord_1214606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214606).length < 2 ^ (prefixWord ++ tailWord_1214606).sum := by decide
  have hdescent : baseEnd_1214606 < baseStart_1214606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214629 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 3]
def baseStart_1214629 : Nat := 118140960795 + 1214629 * 2 ^ 59
def prefixEnd_1214629 : Nat := 4983230072969 + 3 ^ 40 * 1214629 * 2
def baseEnd_1214629 : Nat := 623688493890033492151529

theorem tailTrace_1214629 : CollatzResearch.WordTrace tailWord_1214629 prefixEnd_1214629 623688493890033492151529 := by
  unfold tailWord_1214629
  simp only [CollatzResearch.WordTrace]
  refine ⟨44301159116614049962998941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29534106077742699975332627 44301159116614049962998941)
  ·
    refine ⟨16612934668730268736124603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44301159116614049962998941 16612934668730268736124603)
    ·
      refine ⟨24919402003095403104186905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16612934668730268736124603 24919402003095403104186905)
      ·
        refine ⟨18689551502321552328140179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24919402003095403104186905 18689551502321552328140179)
        ·
          refine ⟨28034327253482328492210269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18689551502321552328140179 28034327253482328492210269)
          ·
            refine ⟨10512872720055873184578851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28034327253482328492210269 10512872720055873184578851)
            ·
              refine ⟨15769309080083809776868277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10512872720055873184578851 15769309080083809776868277)
              ·
                refine ⟨1478372726257857166581401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15769309080083809776868277 1478372726257857166581401)
                ·
                  refine ⟨1108779544693392874936051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1478372726257857166581401 1108779544693392874936051)
                  ·
                    refine ⟨1663169317040089312404077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1108779544693392874936051 1663169317040089312404077)
                    ·
                      refine ⟨623688493890033492151529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1663169317040089312404077 623688493890033492151529)
                      ·
                        rfl

theorem cell23_1214629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_1214629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214629 prefixEnd_1214629 := by exact prefixLift 1214629
  have htrace : WordTrace (prefixWord ++ tailWord_1214629) baseStart_1214629 baseEnd_1214629 := by
    simpa [prefixWord, tailWord_1214629, baseEnd_1214629] using wordTrace_append hprefix tailTrace_1214629
  have hstable : (prefixWord ++ tailWord_1214629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214629).length < 2 ^ (prefixWord ++ tailWord_1214629).sum := by decide
  have hdescent : baseEnd_1214629 < baseStart_1214629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214639 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 1, 3, 2]
def baseStart_1214639 : Nat := 118140960795 + 1214639 * 2 ^ 59
def prefixEnd_1214639 : Nat := 4983230072969 + 3 ^ 40 * 1214639 * 2
def baseEnd_1214639 : Nat := 623693628696578453026483

theorem tailTrace_1214639 : CollatzResearch.WordTrace tailWord_1214639 prefixEnd_1214639 623693628696578453026483 := by
  unfold tailWord_1214639
  simp only [CollatzResearch.WordTrace]
  refine ⟨44301523846577821670862971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29534349231051881113908647 44301523846577821670862971)
  ·
    refine ⟨66452285769866732506294457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44301523846577821670862971 66452285769866732506294457)
    ·
      refine ⟨49839214327400049379720843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66452285769866732506294457 49839214327400049379720843)
      ·
        refine ⟨74758821491100074069581265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49839214327400049379720843 74758821491100074069581265)
        ·
          refine ⟨56069116118325055552185949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74758821491100074069581265 56069116118325055552185949)
          ·
            refine ⟨21025918544371895832069731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56069116118325055552185949 21025918544371895832069731)
            ·
              refine ⟨31538877816557843748104597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21025918544371895832069731 31538877816557843748104597)
              ·
                refine ⟨1478384897651148925692403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31538877816557843748104597 1478384897651148925692403)
                ·
                  refine ⟨2217577346476723388538605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478384897651148925692403 2217577346476723388538605)
                  ·
                    refine ⟨831591504928771270701977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2217577346476723388538605 831591504928771270701977)
                    ·
                      refine ⟨623693628696578453026483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831591504928771270701977 623693628696578453026483)
                      ·
                        rfl

theorem cell23_1214639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 3, 2].length) (baseStart_1214639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214639 prefixEnd_1214639 := by exact prefixLift 1214639
  have htrace : WordTrace (prefixWord ++ tailWord_1214639) baseStart_1214639 baseEnd_1214639 := by
    simpa [prefixWord, tailWord_1214639, baseEnd_1214639] using wordTrace_append hprefix tailTrace_1214639
  have hstable : (prefixWord ++ tailWord_1214639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214639).length < 2 ^ (prefixWord ++ tailWord_1214639).sum := by decide
  have hdescent : baseEnd_1214639 < baseStart_1214639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214655 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_1214655 : Nat := 118140960795 + 1214655 * 2 ^ 59
def prefixEnd_1214655 : Nat := 4983230072969 + 3 ^ 40 * 1214655 * 2
def baseEnd_1214655 : Nat := 623701844387050390426409

theorem tailTrace_1214655 : CollatzResearch.WordTrace tailWord_1214655 prefixEnd_1214655 623701844387050390426409 := by
  unfold tailWord_1214655
  simp only [CollatzResearch.WordTrace]
  refine ⟨44302107414519856403445419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29534738276346570935630279 44302107414519856403445419)
  ·
    refine ⟨66453161121779784605168129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44302107414519856403445419 66453161121779784605168129)
    ·
      refine ⟨49839870841334838453876097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66453161121779784605168129 49839870841334838453876097)
      ·
        refine ⟨37379903131001128840407073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49839870841334838453876097 37379903131001128840407073)
        ·
          refine ⟨28034927348250846630305305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37379903131001128840407073 28034927348250846630305305)
          ·
            refine ⟨21026195511188134972728979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28034927348250846630305305 21026195511188134972728979)
            ·
              refine ⟨31539293266782202459093469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21026195511188134972728979 31539293266782202459093469)
              ·
                refine ⟨11827234975043325922160051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31539293266782202459093469 11827234975043325922160051)
                ·
                  refine ⟨17740852462564988883240077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11827234975043325922160051 17740852462564988883240077)
                  ·
                    refine ⟨6652819673461870831215029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17740852462564988883240077 6652819673461870831215029)
                    ·
                      refine ⟨623701844387050390426409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6652819673461870831215029 623701844387050390426409)
                      ·
                        rfl

theorem cell23_1214655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_1214655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214655 prefixEnd_1214655 := by exact prefixLift 1214655
  have htrace : WordTrace (prefixWord ++ tailWord_1214655) baseStart_1214655 baseEnd_1214655 := by
    simpa [prefixWord, tailWord_1214655, baseEnd_1214655] using wordTrace_append hprefix tailTrace_1214655
  have hstable : (prefixWord ++ tailWord_1214655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214655).length < 2 ^ (prefixWord ++ tailWord_1214655).sum := by decide
  have hdescent : baseEnd_1214655 < baseStart_1214655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214656 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 1, 3, 2]
def baseStart_1214656 : Nat := 118140960795 + 1214656 * 2 ^ 59
def prefixEnd_1214656 : Nat := 4983230072969 + 3 ^ 40 * 1214656 * 2
def baseEnd_1214656 : Nat := 623702357867704886513905

theorem tailTrace_1214656 : CollatzResearch.WordTrace tailWord_1214656 prefixEnd_1214656 623702357867704886513905 := by
  unfold tailWord_1214656
  simp only [CollatzResearch.WordTrace]
  refine ⟨22151071943758116787115911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29534762591677489049487881 22151071943758116787115911)
  ·
    refine ⟨33226607915637175180673867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22151071943758116787115911 33226607915637175180673867)
    ·
      refine ⟨49839911873455762771010801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33226607915637175180673867 49839911873455762771010801)
      ·
        refine ⟨37379933905091822078258101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49839911873455762771010801 37379933905091822078258101)
        ·
          refine ⟨3504368803602358319836697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37379933905091822078258101 3504368803602358319836697)
          ·
            refine ⟨2628276602701768739877523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3504368803602358319836697 2628276602701768739877523)
            ·
              refine ⟨3942414904052653109816285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628276602701768739877523 3942414904052653109816285)
              ·
                refine ⟨1478405589019744916181107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3942414904052653109816285 1478405589019744916181107)
                ·
                  refine ⟨2217608383529617374271661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1478405589019744916181107 2217608383529617374271661)
                  ·
                    refine ⟨831603143823606515351873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2217608383529617374271661 831603143823606515351873)
                    ·
                      refine ⟨623702357867704886513905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831603143823606515351873 623702357867704886513905)
                      ·
                        rfl

theorem cell23_1214656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_1214656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214656 prefixEnd_1214656 := by exact prefixLift 1214656
  have htrace : WordTrace (prefixWord ++ tailWord_1214656) baseStart_1214656 baseEnd_1214656 := by
    simpa [prefixWord, tailWord_1214656, baseEnd_1214656] using wordTrace_append hprefix tailTrace_1214656
  have hstable : (prefixWord ++ tailWord_1214656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214656).length < 2 ^ (prefixWord ++ tailWord_1214656).sum := by decide
  have hdescent : baseEnd_1214656 < baseStart_1214656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214682 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_1214682 : Nat := 118140960795 + 1214682 * 2 ^ 59
def prefixEnd_1214682 : Nat := 4983230072969 + 3 ^ 40 * 1214682 * 2
def baseEnd_1214682 : Nat := 623715708364721784788785

theorem tailTrace_1214682 : CollatzResearch.WordTrace tailWord_1214682 prefixEnd_1214682 623715708364721784788785 := by
  unfold tailWord_1214682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11075773046355510003669575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29535394790281360009785533 11075773046355510003669575)
  ·
    refine ⟨16613659569533265005504363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11075773046355510003669575 16613659569533265005504363)
    ·
      refine ⟨24920489354299897508256545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16613659569533265005504363 24920489354299897508256545)
      ·
        refine ⟨18690367015724923131192409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24920489354299897508256545 18690367015724923131192409)
        ·
          refine ⟨14017775261793692348394307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18690367015724923131192409 14017775261793692348394307)
          ·
            refine ⟨21026662892690538522591461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14017775261793692348394307 21026662892690538522591461)
            ·
              refine ⟨3942499292379475972985899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21026662892690538522591461 3942499292379475972985899)
              ·
                refine ⟨5913748938569213959478849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3942499292379475972985899 5913748938569213959478849)
                ·
                  refine ⟨4435311703926910469609137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5913748938569213959478849 4435311703926910469609137)
                  ·
                    refine ⟨3326483777945182852206853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4435311703926910469609137 3326483777945182852206853)
                    ·
                      refine ⟨623715708364721784788785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3326483777945182852206853 623715708364721784788785)
                      ·
                        rfl

theorem cell23_1214682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_1214682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214682 prefixEnd_1214682 := by exact prefixLift 1214682
  have htrace : WordTrace (prefixWord ++ tailWord_1214682) baseStart_1214682 baseEnd_1214682 := by
    simpa [prefixWord, tailWord_1214682, baseEnd_1214682] using wordTrace_append hprefix tailTrace_1214682
  have hstable : (prefixWord ++ tailWord_1214682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214682).length < 2 ^ (prefixWord ++ tailWord_1214682).sum := by decide
  have hdescent : baseEnd_1214682 < baseStart_1214682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214715 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 7]
def baseStart_1214715 : Nat := 118140960795 + 1214715 * 2 ^ 59
def prefixEnd_1214715 : Nat := 4983230072969 + 3 ^ 40 * 1214715 * 2
def baseEnd_1214715 : Nat := 623732653226320155676133

theorem tailTrace_1214715 : CollatzResearch.WordTrace tailWord_1214715 prefixEnd_1214715 623732653226320155676133 := by
  unfold tailWord_1214715
  simp only [CollatzResearch.WordTrace]
  refine ⟨44304295794302486650629599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29536197196201657767086399 44304295794302486650629599)
  ·
    refine ⟨66456443691453729975944399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44304295794302486650629599 66456443691453729975944399)
    ·
      refine ⟨99684665537180594963916599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66456443691453729975944399 99684665537180594963916599)
      ·
        refine ⟨149526998305770892445874899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99684665537180594963916599 149526998305770892445874899)
        ·
          refine ⟨224290497458656338668812349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149526998305770892445874899 224290497458656338668812349)
          ·
            refine ⟨84108936546996127000804631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224290497458656338668812349 84108936546996127000804631)
            ·
              refine ⟨126163404820494190501206947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84108936546996127000804631 126163404820494190501206947)
              ·
                refine ⟨189245107230741285751810421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126163404820494190501206947 189245107230741285751810421)
                ·
                  refine ⟨17741728802881995539232227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189245107230741285751810421 17741728802881995539232227)
                  ·
                    refine ⟨26612593204322993308848341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17741728802881995539232227 26612593204322993308848341)
                    ·
                      refine ⟨623732653226320155676133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26612593204322993308848341 623732653226320155676133)
                      ·
                        rfl

theorem cell23_1214715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_1214715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214715 prefixEnd_1214715 := by exact prefixLift 1214715
  have htrace : WordTrace (prefixWord ++ tailWord_1214715) baseStart_1214715 baseEnd_1214715 := by
    simpa [prefixWord, tailWord_1214715, baseEnd_1214715] using wordTrace_append hprefix tailTrace_1214715
  have hstable : (prefixWord ++ tailWord_1214715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214715).length < 2 ^ (prefixWord ++ tailWord_1214715).sum := by decide
  have hdescent : baseEnd_1214715 < baseStart_1214715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214732 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_1214732 : Nat := 118140960795 + 1214732 * 2 ^ 59
def prefixEnd_1214732 : Nat := 4983230072969 + 3 ^ 40 * 1214732 * 2
def baseEnd_1214732 : Nat := 623741382397446589163555

theorem tailTrace_1214732 : CollatzResearch.WordTrace tailWord_1214732 prefixEnd_1214732 623741382397446589163555 := by
  unfold tailWord_1214732
  simp only [CollatzResearch.WordTrace]
  refine ⟨22152457917620449276999225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29536610556827265702665633 22152457917620449276999225)
  ·
    refine ⟨16614343438215336957749419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22152457917620449276999225 16614343438215336957749419)
    ·
      refine ⟨24921515157323005436624129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16614343438215336957749419 24921515157323005436624129)
      ·
        refine ⟨18691136367992254077468097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24921515157323005436624129 18691136367992254077468097)
        ·
          refine ⟨14018352275994190558101073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18691136367992254077468097 14018352275994190558101073)
          ·
            refine ⟨10513764206995642918575805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14018352275994190558101073 10513764206995642918575805)
            ·
              refine ⟨3942661577623366094465927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10513764206995642918575805 3942661577623366094465927)
              ·
                refine ⟨5913992366435049141698891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3942661577623366094465927 5913992366435049141698891)
                ·
                  refine ⟨8870988549652573712548337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5913992366435049141698891 8870988549652573712548337)
                  ·
                    refine ⟨6653241412239430284411253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8870988549652573712548337 6653241412239430284411253)
                    ·
                      refine ⟨623741382397446589163555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6653241412239430284411253 623741382397446589163555)
                      ·
                        rfl

theorem cell23_1214732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_1214732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214732 prefixEnd_1214732 := by exact prefixLift 1214732
  have htrace : WordTrace (prefixWord ++ tailWord_1214732) baseStart_1214732 baseEnd_1214732 := by
    simpa [prefixWord, tailWord_1214732, baseEnd_1214732] using wordTrace_append hprefix tailTrace_1214732
  have hstable : (prefixWord ++ tailWord_1214732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214732).length < 2 ^ (prefixWord ++ tailWord_1214732).sum := by decide
  have hdescent : baseEnd_1214732 < baseStart_1214732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214843 : List Nat := [1, 1, 1, 1, 1, 7, 2, 4, 1, 1, 3]
def baseStart_1214843 : Nat := 118140960795 + 1214843 * 2 ^ 59
def prefixEnd_1214843 : Nat := 4983230072969 + 3 ^ 40 * 1214843 * 2
def baseEnd_1214843 : Nat := 623798378750095654875545

theorem tailTrace_1214843 : CollatzResearch.WordTrace tailWord_1214843 prefixEnd_1214843 623798378750095654875545 := by
  unfold tailWord_1214843
  simp only [CollatzResearch.WordTrace]
  refine ⟨44308964337838764511289183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29539309558559176340859455 44308964337838764511289183)
  ·
    refine ⟨66463446506758146766933775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44308964337838764511289183 66463446506758146766933775)
    ·
      refine ⟨99695169760137220150400663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66463446506758146766933775 99695169760137220150400663)
      ·
        refine ⟨149542754640205830225600995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99695169760137220150400663 149542754640205830225600995)
        ·
          refine ⟨224314131960308745338401493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149542754640205830225600995 224314131960308745338401493)
          ·
            refine ⟨5257362467819736218868785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 224314131960308745338401493 5257362467819736218868785)
            ·
              refine ⟨3943021850864802164151589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5257362467819736218868785 3943021850864802164151589)
              ·
                refine ⟨739316597037150405778423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3943021850864802164151589 739316597037150405778423)
                ·
                  refine ⟨1108974895555725608667635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739316597037150405778423 1108974895555725608667635)
                  ·
                    refine ⟨1663462343333588413001453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1108974895555725608667635 1663462343333588413001453)
                    ·
                      refine ⟨623798378750095654875545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1663462343333588413001453 623798378750095654875545)
                      ·
                        rfl

theorem cell23_1214843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 1, 1, 3].length) (baseStart_1214843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214843 prefixEnd_1214843 := by exact prefixLift 1214843
  have htrace : WordTrace (prefixWord ++ tailWord_1214843) baseStart_1214843 baseEnd_1214843 := by
    simpa [prefixWord, tailWord_1214843, baseEnd_1214843] using wordTrace_append hprefix tailTrace_1214843
  have hstable : (prefixWord ++ tailWord_1214843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214843).length < 2 ^ (prefixWord ++ tailWord_1214843).sum := by decide
  have hdescent : baseEnd_1214843 < baseStart_1214843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214850 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1214850 : Nat := 118140960795 + 1214850 * 2 ^ 59
def prefixEnd_1214850 : Nat := 4983230072969 + 3 ^ 40 * 1214850 * 2
def baseEnd_1214850 : Nat := 69311330346075236387557

theorem tailTrace_1214850 : CollatzResearch.WordTrace tailWord_1214850 prefixEnd_1214850 69311330346075236387557 := by
  unfold tailWord_1214850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11077304912203351176698501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29539479765875603137862669 11077304912203351176698501)
  ·
    refine ⟨2076994671038128345630969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11077304912203351176698501 2076994671038128345630969)
    ·
      refine ⟨1557746003278596259223227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2076994671038128345630969 1557746003278596259223227)
      ·
        refine ⟨2336619004917894388834841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1557746003278596259223227 2336619004917894388834841)
        ·
          refine ⟨1752464253688420791626131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2336619004917894388834841 1752464253688420791626131)
          ·
            refine ⟨2628696380532631187439197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752464253688420791626131 2628696380532631187439197)
            ·
              refine ⟨985761142699736695289699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2628696380532631187439197 985761142699736695289699)
              ·
                refine ⟨1478641714049605042934549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 985761142699736695289699 1478641714049605042934549)
                ·
                  refine ⟨69311330346075236387557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1478641714049605042934549 69311330346075236387557)
                  ·
                    rfl

theorem cell23_1214850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1214850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214850 prefixEnd_1214850 := by exact prefixLift 1214850
  have htrace : WordTrace (prefixWord ++ tailWord_1214850) baseStart_1214850 baseEnd_1214850 := by
    simpa [prefixWord, tailWord_1214850, baseEnd_1214850] using wordTrace_append hprefix tailTrace_1214850
  have hstable : (prefixWord ++ tailWord_1214850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214850).length < 2 ^ (prefixWord ++ tailWord_1214850).sum := by decide
  have hdescent : baseEnd_1214850 < baseStart_1214850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214859 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 1, 6]
def baseStart_1214859 : Nat := 118140960795 + 1214859 * 2 ^ 59
def prefixEnd_1214859 : Nat := 4983230072969 + 3 ^ 40 * 1214859 * 2
def baseEnd_1214859 : Nat := 207935531480189197425157

theorem tailTrace_1214859 : CollatzResearch.WordTrace tailWord_1214859 prefixEnd_1214859 207935531480189197425157 := by
  unfold tailWord_1214859
  simp only [CollatzResearch.WordTrace]
  refine ⟨44309547905780799243871631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29539698603853866162581087 44309547905780799243871631)
  ·
    refine ⟨66464321858671198865807447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44309547905780799243871631 66464321858671198865807447)
    ·
      refine ⟨99696482788006798298711171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66464321858671198865807447 99696482788006798298711171)
      ·
        refine ⟨149544724182010197448066757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99696482788006798298711171 149544724182010197448066757)
        ·
          refine ⟨28039635784126912021512517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149544724182010197448066757 28039635784126912021512517)
          ·
            refine ⟨5257431709523796004033597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28039635784126912021512517 5257431709523796004033597)
            ·
              refine ⟨1971536891071423501512599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5257431709523796004033597 1971536891071423501512599)
              ·
                refine ⟨2957305336607135252268899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971536891071423501512599 2957305336607135252268899)
                ·
                  refine ⟨4435958004910702878403349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957305336607135252268899 4435958004910702878403349)
                  ·
                    refine ⟨207935531480189197425157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4435958004910702878403349 207935531480189197425157)
                    ·
                      rfl

theorem cell23_1214859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 6].length) (baseStart_1214859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214859 prefixEnd_1214859 := by exact prefixLift 1214859
  have htrace : WordTrace (prefixWord ++ tailWord_1214859) baseStart_1214859 baseEnd_1214859 := by
    simpa [prefixWord, tailWord_1214859, baseEnd_1214859] using wordTrace_append hprefix tailTrace_1214859
  have hstable : (prefixWord ++ tailWord_1214859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214859).length < 2 ^ (prefixWord ++ tailWord_1214859).sum := by decide
  have hdescent : baseEnd_1214859 < baseStart_1214859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214877 : List Nat := [1, 4, 2, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_1214877 : Nat := 118140960795 + 1214877 * 2 ^ 59
def prefixEnd_1214877 : Nat := 4983230072969 + 3 ^ 40 * 1214877 * 2
def baseEnd_1214877 : Nat := 623815837092348521850389

theorem tailTrace_1214877 : CollatzResearch.WordTrace tailWord_1214877 prefixEnd_1214877 623815837092348521850389 := by
  unfold tailWord_1214877
  simp only [CollatzResearch.WordTrace]
  refine ⟨44310204419715588318026885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29540136279810392212017923 44310204419715588318026885)
  ·
    refine ⟨8308163328696672809630041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44310204419715588318026885 8308163328696672809630041)
    ·
      refine ⟨6231122496522504607222531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8308163328696672809630041 6231122496522504607222531)
      ·
        refine ⟨9346683744783756910833797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231122496522504607222531 9346683744783756910833797)
        ·
          refine ⟨1752503202146954420781337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9346683744783756910833797 1752503202146954420781337)
          ·
            refine ⟨1314377401610215815586003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1752503202146954420781337 1314377401610215815586003)
            ·
              refine ⟨1971566102415323723379005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314377401610215815586003 1971566102415323723379005)
              ·
                refine ⟨739337288405746396267127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1971566102415323723379005 739337288405746396267127)
                ·
                  refine ⟨1109005932608619594400691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739337288405746396267127 1109005932608619594400691)
                  ·
                    refine ⟨1663508898912929391601037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1109005932608619594400691 1663508898912929391601037)
                    ·
                      refine ⟨623815837092348521850389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1663508898912929391601037 623815837092348521850389)
                      ·
                        rfl

theorem cell23_1214877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_1214877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214877 prefixEnd_1214877 := by exact prefixLift 1214877
  have htrace : WordTrace (prefixWord ++ tailWord_1214877) baseStart_1214877 baseEnd_1214877 := by
    simpa [prefixWord, tailWord_1214877, baseEnd_1214877] using wordTrace_append hprefix tailTrace_1214877
  have hstable : (prefixWord ++ tailWord_1214877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214877).length < 2 ^ (prefixWord ++ tailWord_1214877).sum := by decide
  have hdescent : baseEnd_1214877 < baseStart_1214877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214879 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1214879 : Nat := 118140960795 + 1214879 * 2 ^ 59
def prefixEnd_1214879 : Nat := 4983230072969 + 3 ^ 40 * 1214879 * 2
def baseEnd_1214879 : Nat := 623816864053657514025379

theorem tailTrace_1214879 : CollatzResearch.WordTrace tailWord_1214879 prefixEnd_1214879 623816864053657514025379 := by
  unfold tailWord_1214879
  simp only [CollatzResearch.WordTrace]
  refine ⟨44310277365708342659599691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29540184910472228439733127 44310277365708342659599691)
  ·
    refine ⟨66465416048562513989399537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44310277365708342659599691 66465416048562513989399537)
    ·
      refine ⟨49849062036421885492049653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66465416048562513989399537 49849062036421885492049653)
      ·
        refine ⟨4673349565914551764879655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49849062036421885492049653 4673349565914551764879655)
        ·
          refine ⟨7010024348871827647319483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4673349565914551764879655 7010024348871827647319483)
          ·
            refine ⟨10515036523307741470979225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010024348871827647319483 10515036523307741470979225)
            ·
              refine ⟨7886277392480806103234419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10515036523307741470979225 7886277392480806103234419)
              ·
                refine ⟨11829416088721209154851629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7886277392480806103234419 11829416088721209154851629)
                ·
                  refine ⟨4436031033270453433069361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11829416088721209154851629 4436031033270453433069361)
                  ·
                    refine ⟨3327023274952840074802021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4436031033270453433069361 3327023274952840074802021)
                    ·
                      refine ⟨623816864053657514025379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3327023274952840074802021 623816864053657514025379)
                      ·
                        rfl

theorem cell23_1214879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1214879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214879 prefixEnd_1214879 := by exact prefixLift 1214879
  have htrace : WordTrace (prefixWord ++ tailWord_1214879) baseStart_1214879 baseEnd_1214879 := by
    simpa [prefixWord, tailWord_1214879, baseEnd_1214879] using wordTrace_append hprefix tailTrace_1214879
  have hstable : (prefixWord ++ tailWord_1214879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214879).length < 2 ^ (prefixWord ++ tailWord_1214879).sum := by decide
  have hdescent : baseEnd_1214879 < baseStart_1214879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214956 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 3, 4, 2]
def baseStart_1214956 : Nat := 118140960795 + 1214956 * 2 ^ 59
def prefixEnd_1214956 : Nat := 4983230072969 + 3 ^ 40 * 1214956 * 2
def baseEnd_1214956 : Nat := 623856402064053712762525

theorem tailTrace_1214956 : CollatzResearch.WordTrace tailWord_1214956 prefixEnd_1214956 623856402064053712762525 := by
  unfold tailWord_1214956
  simp only [CollatzResearch.WordTrace]
  refine ⟨22156542893214692405076361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29542057190952923206768481 22156542893214692405076361)
  ·
    refine ⟨16617407169911019303807271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22156542893214692405076361 16617407169911019303807271)
    ·
      refine ⟨24926110754866528955710907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16617407169911019303807271 24926110754866528955710907)
      ·
        refine ⟨37389166132299793433566361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24926110754866528955710907 37389166132299793433566361)
        ·
          refine ⟨28041874599224845075174771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37389166132299793433566361 28041874599224845075174771)
          ·
            refine ⟨42062811898837267612762157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28041874599224845075174771 42062811898837267612762157)
            ·
              refine ⟨15773554462063975354785809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42062811898837267612762157 15773554462063975354785809)
              ·
                refine ⟨11830165846547981516089357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15773554462063975354785809 11830165846547981516089357)
                ·
                  refine ⟨4436312192455493068533509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11830165846547981516089357 4436312192455493068533509)
                  ·
                    refine ⟨831808536085404950350033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4436312192455493068533509 831808536085404950350033)
                    ·
                      refine ⟨623856402064053712762525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831808536085404950350033 623856402064053712762525)
                      ·
                        rfl

theorem cell23_1214956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_1214956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214956 prefixEnd_1214956 := by exact prefixLift 1214956
  have htrace : WordTrace (prefixWord ++ tailWord_1214956) baseStart_1214956 baseEnd_1214956 := by
    simpa [prefixWord, tailWord_1214956, baseEnd_1214956] using wordTrace_append hprefix tailTrace_1214956
  have hstable : (prefixWord ++ tailWord_1214956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214956).length < 2 ^ (prefixWord ++ tailWord_1214956).sum := by decide
  have hdescent : baseEnd_1214956 < baseStart_1214956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214966 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 2, 6]
def baseStart_1214966 : Nat := 118140960795 + 1214966 * 2 ^ 59
def prefixEnd_1214966 : Nat := 4983230072969 + 3 ^ 40 * 1214966 * 2
def baseEnd_1214966 : Nat := 207953845623532891212493

theorem tailTrace_1214966 : CollatzResearch.WordTrace tailWord_1214966 prefixEnd_1214966 207953845623532891212493 := by
  unfold tailWord_1214966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769590657274572282376047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29542300344262104345344501 2769590657274572282376047)
  ·
    refine ⟨4154385985911858423564071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2769590657274572282376047 4154385985911858423564071)
    ·
      refine ⟨6231578978867787635346107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4154385985911858423564071 6231578978867787635346107)
      ·
        refine ⟨9347368468301681453019161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6231578978867787635346107 9347368468301681453019161)
        ·
          refine ⟨7010526351226261089764371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9347368468301681453019161 7010526351226261089764371)
          ·
            refine ⟨10515789526839391634646557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7010526351226261089764371 10515789526839391634646557)
            ·
              refine ⟨3943421072564771862992459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10515789526839391634646557 3943421072564771862992459)
              ·
                refine ⟨5915131608847157794488689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943421072564771862992459 5915131608847157794488689)
                ·
                  refine ⟨4436348706635368345866517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5915131608847157794488689 4436348706635368345866517)
                  ·
                    refine ⟨207953845623532891212493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4436348706635368345866517 207953845623532891212493)
                    ·
                      rfl

theorem cell23_1214966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_1214966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214966 prefixEnd_1214966 := by exact prefixLift 1214966
  have htrace : WordTrace (prefixWord ++ tailWord_1214966) baseStart_1214966 baseEnd_1214966 := by
    simpa [prefixWord, tailWord_1214966, baseEnd_1214966] using wordTrace_append hprefix tailTrace_1214966
  have hstable : (prefixWord ++ tailWord_1214966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214966).length < 2 ^ (prefixWord ++ tailWord_1214966).sum := by decide
  have hdescent : baseEnd_1214966 < baseStart_1214966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214969 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1214969 : Nat := 118140960795 + 1214969 * 2 ^ 59
def prefixEnd_1214969 : Nat := 4983230072969 + 3 ^ 40 * 1214969 * 2
def baseEnd_1214969 : Nat := 623863077312562161899965

theorem tailTrace_1214969 : CollatzResearch.WordTrace tailWord_1214969 prefixEnd_1214969 623863077312562161899965 := by
  unfold tailWord_1214969
  simp only [CollatzResearch.WordTrace]
  refine ⟨44313559935382288030375961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29542373290254858686917307 44313559935382288030375961)
  ·
    refine ⟨33235169951536716022781971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44313559935382288030375961 33235169951536716022781971)
    ·
      refine ⟨49852754927305074034172957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33235169951536716022781971 49852754927305074034172957)
      ·
        refine ⟨18694783097739402762814859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49852754927305074034172957 18694783097739402762814859)
        ·
          refine ⟨28042174646609104144222289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18694783097739402762814859 28042174646609104144222289)
          ·
            refine ⟨21031630984956828108166717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28042174646609104144222289 21031630984956828108166717)
            ·
              refine ⟨7886861619358810540562519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21031630984956828108166717 7886861619358810540562519)
              ·
                refine ⟨11830292429038215810843779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7886861619358810540562519 11830292429038215810843779)
                ·
                  refine ⟨17745438643557323716265669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11830292429038215810843779 17745438643557323716265669)
                  ·
                    refine ⟨3327269745666998196799813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17745438643557323716265669 3327269745666998196799813)
                    ·
                      refine ⟨623863077312562161899965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3327269745666998196799813 623863077312562161899965)
                      ·
                        rfl

theorem cell23_1214969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1214969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214969 prefixEnd_1214969 := by exact prefixLift 1214969
  have htrace : WordTrace (prefixWord ++ tailWord_1214969) baseStart_1214969 baseEnd_1214969 := by
    simpa [prefixWord, tailWord_1214969, baseEnd_1214969] using wordTrace_append hprefix tailTrace_1214969
  have hstable : (prefixWord ++ tailWord_1214969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214969).length < 2 ^ (prefixWord ++ tailWord_1214969).sum := by decide
  have hdescent : baseEnd_1214969 < baseStart_1214969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214973 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_1214973 : Nat := 118140960795 + 1214973 * 2 ^ 59
def prefixEnd_1214973 : Nat := 4983230072969 + 3 ^ 40 * 1214973 * 2
def baseEnd_1214973 : Nat := 623865131235180146249947

theorem tailTrace_1214973 : CollatzResearch.WordTrace tailWord_1214973 prefixEnd_1214973 623865131235180146249947 := by
  unfold tailWord_1214973
  simp only [CollatzResearch.WordTrace]
  refine ⟨44313705827367796713521573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29542470551578531142347715 44313705827367796713521573)
  ·
    refine ⟨8308819842631461883785295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44313705827367796713521573 8308819842631461883785295)
    ·
      refine ⟨12463229763947192825677943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8308819842631461883785295 12463229763947192825677943)
      ·
        refine ⟨18694844645920789238516915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12463229763947192825677943 18694844645920789238516915)
        ·
          refine ⟨28042266968881183857775373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18694844645920789238516915 28042266968881183857775373)
          ·
            refine ⟨10515850113330443946665765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28042266968881183857775373 10515850113330443946665765)
            ·
              refine ⟨1971721896249458239999831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10515850113330443946665765 1971721896249458239999831)
              ·
                refine ⟨2957582844374187359999747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971721896249458239999831 2957582844374187359999747)
                ·
                  refine ⟨4436374266561281039999621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2957582844374187359999747 4436374266561281039999621)
                  ·
                    refine ⟨831820174980240194999929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4436374266561281039999621 831820174980240194999929)
                    ·
                      refine ⟨623865131235180146249947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831820174980240194999929 623865131235180146249947)
                      ·
                        rfl

theorem cell23_1214973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_1214973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214973 prefixEnd_1214973 := by exact prefixLift 1214973
  have htrace : WordTrace (prefixWord ++ tailWord_1214973) baseStart_1214973 baseEnd_1214973 := by
    simpa [prefixWord, tailWord_1214973, baseEnd_1214973] using wordTrace_append hprefix tailTrace_1214973
  have hstable : (prefixWord ++ tailWord_1214973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214973).length < 2 ^ (prefixWord ++ tailWord_1214973).sum := by decide
  have hdescent : baseEnd_1214973 < baseStart_1214973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214979 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 7]
def baseStart_1214979 : Nat := 118140960795 + 1214979 * 2 ^ 59
def prefixEnd_1214979 : Nat := 4983230072969 + 3 ^ 40 * 1214979 * 2
def baseEnd_1214979 : Nat := 69318690235456346974991

theorem tailTrace_1214979 : CollatzResearch.WordTrace tailWord_1214979 prefixEnd_1214979 69318690235456346974991 := by
  unfold tailWord_1214979
  simp only [CollatzResearch.WordTrace]
  refine ⟨44313924665346059738239991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29542616443564039825493327 44313924665346059738239991)
  ·
    refine ⟨66470886998019089607359987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44313924665346059738239991 66470886998019089607359987)
    ·
      refine ⟨99706330497028634411039981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66470886998019089607359987 99706330497028634411039981)
      ·
        refine ⟨37389873936385737904139993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99706330497028634411039981 37389873936385737904139993)
        ·
          refine ⟨28042405452289303428104995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37389873936385737904139993 28042405452289303428104995)
          ·
            refine ⟨42063608178433955142157493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28042405452289303428104995 42063608178433955142157493)
            ·
              refine ⟨3943463266728183294577265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42063608178433955142157493 3943463266728183294577265)
              ·
                refine ⟨2957597450046137470932949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3943463266728183294577265 2957597450046137470932949)
                ·
                  refine ⟨69318690235456346974991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2957597450046137470932949 69318690235456346974991)
                  ·
                    rfl

theorem cell23_1214979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 7].length) (baseStart_1214979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1214979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1214979 prefixEnd_1214979 := by exact prefixLift 1214979
  have htrace : WordTrace (prefixWord ++ tailWord_1214979) baseStart_1214979 baseEnd_1214979 := by
    simpa [prefixWord, tailWord_1214979, baseEnd_1214979] using wordTrace_append hprefix tailTrace_1214979
  have hstable : (prefixWord ++ tailWord_1214979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214979).length < 2 ^ (prefixWord ++ tailWord_1214979).sum := by decide
  have hdescent : baseEnd_1214979 < baseStart_1214979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215019 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 5]
def baseStart_1215019 : Nat := 118140960795 + 1215019 * 2 ^ 59
def prefixEnd_1215019 : Nat := 4983230072969 + 3 ^ 40 * 1215019 * 2
def baseEnd_1215019 : Nat := 623888751345286966274735

theorem tailTrace_1215019 : CollatzResearch.WordTrace tailWord_1215019 prefixEnd_1215019 623888751345286966274735 := by
  unfold tailWord_1215019
  simp only [CollatzResearch.WordTrace]
  refine ⟨44315383585201146569696111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29543589056800764379797407 44315383585201146569696111)
  ·
    refine ⟨66473075377801719854544167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44315383585201146569696111 66473075377801719854544167)
    ·
      refine ⟨99709613066702579781816251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66473075377801719854544167 99709613066702579781816251)
      ·
        refine ⟨149564419600053869672724377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99709613066702579781816251 149564419600053869672724377)
        ·
          refine ⟨112173314700040402254543283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149564419600053869672724377 112173314700040402254543283)
          ·
            refine ⟨168259972050060603381814925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112173314700040402254543283 168259972050060603381814925)
            ·
              refine ⟨63097489518772726268180597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168259972050060603381814925 63097489518772726268180597)
              ·
                refine ⟨5915389642384943087641931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63097489518772726268180597 5915389642384943087641931)
                ·
                  refine ⟨8873084463577414631462897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5915389642384943087641931 8873084463577414631462897)
                  ·
                    refine ⟨6654813347683060973597173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8873084463577414631462897 6654813347683060973597173)
                    ·
                      refine ⟨623888751345286966274735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6654813347683060973597173 623888751345286966274735)
                      ·
                        rfl

theorem cell23_1215019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_1215019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215019 prefixEnd_1215019 := by exact prefixLift 1215019
  have htrace : WordTrace (prefixWord ++ tailWord_1215019) baseStart_1215019 baseEnd_1215019 := by
    simpa [prefixWord, tailWord_1215019, baseEnd_1215019] using wordTrace_append hprefix tailTrace_1215019
  have hstable : (prefixWord ++ tailWord_1215019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215019).length < 2 ^ (prefixWord ++ tailWord_1215019).sum := by decide
  have hdescent : baseEnd_1215019 < baseStart_1215019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215039 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 2, 8]
def baseStart_1215039 : Nat := 118140960795 + 1215039 * 2 ^ 59
def prefixEnd_1215039 : Nat := 4983230072969 + 3 ^ 40 * 1215039 * 2
def baseEnd_1215039 : Nat := 207966340319458962674881

theorem tailTrace_1215039 : CollatzResearch.WordTrace tailWord_1215039 prefixEnd_1215039 207966340319458962674881 := by
  unfold tailWord_1215039
  simp only [CollatzResearch.WordTrace]
  refine ⟨44316113045128689985424171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29544075363419126656949447 44316113045128689985424171)
  ·
    refine ⟨66474169567693034978136257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44316113045128689985424171 66474169567693034978136257)
    ·
      refine ⟨49855627175769776233602193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66474169567693034978136257 49855627175769776233602193)
      ·
        refine ⟨37391720381827332175201645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49855627175769776233602193 37391720381827332175201645)
        ·
          refine ⟨14021895143185249565700617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37391720381827332175201645 14021895143185249565700617)
          ·
            refine ⟨10516421357388937174275463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14021895143185249565700617 10516421357388937174275463)
            ·
              refine ⟨15774632036083405761413195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10516421357388937174275463 15774632036083405761413195)
              ·
                refine ⟨23661948054125108642119793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15774632036083405761413195 23661948054125108642119793)
                ·
                  refine ⟨17746461040593831481589845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23661948054125108642119793 17746461040593831481589845)
                  ·
                    refine ⟨207966340319458962674881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17746461040593831481589845 207966340319458962674881)
                    ·
                      rfl

theorem cell23_1215039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_1215039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215039 prefixEnd_1215039 := by exact prefixLift 1215039
  have htrace : WordTrace (prefixWord ++ tailWord_1215039) baseStart_1215039 baseEnd_1215039 := by
    simpa [prefixWord, tailWord_1215039, baseEnd_1215039] using wordTrace_append hprefix tailTrace_1215039
  have hstable : (prefixWord ++ tailWord_1215039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215039).length < 2 ^ (prefixWord ++ tailWord_1215039).sum := by decide
  have hdescent : baseEnd_1215039 < baseStart_1215039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215049 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_1215049 : Nat := 118140960795 + 1215049 * 2 ^ 59
def prefixEnd_1215049 : Nat := 4983230072969 + 3 ^ 40 * 1215049 * 2
def baseEnd_1215049 : Nat := 623904155764921848899597

theorem tailTrace_1215049 : CollatzResearch.WordTrace tailWord_1215049 prefixEnd_1215049 623904155764921848899597 := by
  unfold tailWord_1215049
  simp only [CollatzResearch.WordTrace]
  refine ⟨44316477775092461693288201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29544318516728307795525467 44316477775092461693288201)
  ·
    refine ⟨33237358331319346269966151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44316477775092461693288201 33237358331319346269966151)
    ·
      refine ⟨49856037496979019404949227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33237358331319346269966151 49856037496979019404949227)
      ·
        refine ⟨74784056245468529107423841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49856037496979019404949227 74784056245468529107423841)
        ·
          refine ⟨56088042184101396830567881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74784056245468529107423841 56088042184101396830567881)
          ·
            refine ⟨42066031638076047622925911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56088042184101396830567881 42066031638076047622925911)
            ·
              refine ⟨63099047457114071434388867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42066031638076047622925911 63099047457114071434388867)
              ·
                refine ⟨94648571185671107151583301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63099047457114071434388867 94648571185671107151583301)
                ·
                  refine ⟨17746607097313332590921869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94648571185671107151583301 17746607097313332590921869)
                  ·
                    refine ⟨6654977661492499721595701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17746607097313332590921869 6654977661492499721595701)
                    ·
                      refine ⟨623904155764921848899597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6654977661492499721595701 623904155764921848899597)
                      ·
                        rfl

theorem cell23_1215049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_1215049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215049 prefixEnd_1215049 := by exact prefixLift 1215049
  have htrace : WordTrace (prefixWord ++ tailWord_1215049) baseStart_1215049 baseEnd_1215049 := by
    simpa [prefixWord, tailWord_1215049, baseEnd_1215049] using wordTrace_append hprefix tailTrace_1215049
  have hstable : (prefixWord ++ tailWord_1215049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215049).length < 2 ^ (prefixWord ++ tailWord_1215049).sum := by decide
  have hdescent : baseEnd_1215049 < baseStart_1215049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215073 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 3, 4]
def baseStart_1215073 : Nat := 118140960795 + 1215073 * 2 ^ 59
def prefixEnd_1215073 : Nat := 4983230072969 + 3 ^ 40 * 1215073 * 2
def baseEnd_1215073 : Nat := 207972159766876584999829

theorem tailTrace_1215073 : CollatzResearch.WordTrace tailWord_1215073 prefixEnd_1215073 207972159766876584999829 := by
  unfold tailWord_1215073
  simp only [CollatzResearch.WordTrace]
  refine ⟨44317353127005513792161873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29544902084670342528107915 44317353127005513792161873)
  ·
    refine ⟨33238014845254135344121405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44317353127005513792161873 33238014845254135344121405)
    ·
      refine ⟨12464255566970300754045527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33238014845254135344121405 12464255566970300754045527)
      ·
        refine ⟨18696383350455451131068291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12464255566970300754045527 18696383350455451131068291)
        ·
          refine ⟨28044575025683176696602437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18696383350455451131068291 28044575025683176696602437)
          ·
            refine ⟨5258357817315595630612957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28044575025683176696602437 5258357817315595630612957)
            ·
              refine ⟨1971884181493348361479859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5258357817315595630612957 1971884181493348361479859)
              ·
                refine ⟨2957826272240022542219789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971884181493348361479859 2957826272240022542219789)
                ·
                  refine ⟨1109184852090008453332421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2957826272240022542219789 1109184852090008453332421)
                  ·
                    refine ⟨207972159766876584999829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1109184852090008453332421 207972159766876584999829)
                    ·
                      rfl

theorem cell23_1215073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_1215073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215073 prefixEnd_1215073 := by exact prefixLift 1215073
  have htrace : WordTrace (prefixWord ++ tailWord_1215073) baseStart_1215073 baseEnd_1215073 := by
    simpa [prefixWord, tailWord_1215073, baseEnd_1215073] using wordTrace_append hprefix tailTrace_1215073
  have hstable : (prefixWord ++ tailWord_1215073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215073).length < 2 ^ (prefixWord ++ tailWord_1215073).sum := by decide
  have hdescent : baseEnd_1215073 < baseStart_1215073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215124 : List Nat := [2, 4, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_1215124 : Nat := 118140960795 + 1215124 * 2 ^ 59
def prefixEnd_1215124 : Nat := 4983230072969 + 3 ^ 40 * 1215124 * 2
def baseEnd_1215124 : Nat := 207980888938003018487251

theorem tailTrace_1215124 : CollatzResearch.WordTrace tailWord_1215124 prefixEnd_1215124 207980888938003018487251 := by
  unfold tailWord_1215124
  simp only [CollatzResearch.WordTrace]
  refine ⟨22159606624910374751134213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29546142166547166334845617 22159606624910374751134213)
  ·
    refine ⟨4154926242170695265837665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22159606624910374751134213 4154926242170695265837665)
    ·
      refine ⟨3116194681628021449378249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4154926242170695265837665 3116194681628021449378249)
      ·
        refine ⟨2337146011221016087033687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3116194681628021449378249 2337146011221016087033687)
        ·
          refine ⟨3505719016831524130550531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337146011221016087033687 3505719016831524130550531)
          ·
            refine ⟨5258578525247286195825797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505719016831524130550531 5258578525247286195825797)
            ·
              refine ⟨985983473483866161717337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5258578525247286195825797 985983473483866161717337)
              ·
                refine ⟨739487605112899621288003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 985983473483866161717337 739487605112899621288003)
                ·
                  refine ⟨1109231407669349431932005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739487605112899621288003 1109231407669349431932005)
                  ·
                    refine ⟨207980888938003018487251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1109231407669349431932005 207980888938003018487251)
                    ·
                      rfl

theorem cell23_1215124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_1215124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215124 prefixEnd_1215124 := by exact prefixLift 1215124
  have htrace : WordTrace (prefixWord ++ tailWord_1215124) baseStart_1215124 baseEnd_1215124 := by
    simpa [prefixWord, tailWord_1215124, baseEnd_1215124] using wordTrace_append hprefix tailTrace_1215124
  have hstable : (prefixWord ++ tailWord_1215124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215124).length < 2 ^ (prefixWord ++ tailWord_1215124).sum := by decide
  have hdescent : baseEnd_1215124 < baseStart_1215124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215150 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1215150 : Nat := 118140960795 + 1215150 * 2 ^ 59
def prefixEnd_1215150 : Nat := 4983230072969 + 3 ^ 40 * 1215150 * 2
def baseEnd_1215150 : Nat := 207985339103675317912211

theorem tailTrace_1215150 : CollatzResearch.WordTrace tailWord_1215150 prefixEnd_1215150 207985339103675317912211 := by
  unfold tailWord_1215150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5540020193465819492839363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29546774365151037295143269 5540020193465819492839363)
  ·
    refine ⟨8310030290198729239259045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5540020193465819492839363 8310030290198729239259045)
    ·
      refine ⟨1558130679412261732361071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8310030290198729239259045 1558130679412261732361071)
      ·
        refine ⟨2337196019118392598541607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558130679412261732361071 2337196019118392598541607)
        ·
          refine ⟨3505794028677588897812411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337196019118392598541607 3505794028677588897812411)
          ·
            refine ⟨5258691043016383346718617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505794028677588897812411 5258691043016383346718617)
            ·
              refine ⟨3944018282262287510038963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5258691043016383346718617 3944018282262287510038963)
              ·
                refine ⟨5916027423393431265058445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944018282262287510038963 5916027423393431265058445)
                ·
                  refine ⟨2218510283772536724396917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5916027423393431265058445 2218510283772536724396917)
                  ·
                    refine ⟨207985339103675317912211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2218510283772536724396917 207985339103675317912211)
                    ·
                      rfl

theorem cell23_1215150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1215150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215150 prefixEnd_1215150 := by exact prefixLift 1215150
  have htrace : WordTrace (prefixWord ++ tailWord_1215150) baseStart_1215150 baseEnd_1215150 := by
    simpa [prefixWord, tailWord_1215150, baseEnd_1215150] using wordTrace_append hprefix tailTrace_1215150
  have hstable : (prefixWord ++ tailWord_1215150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215150).length < 2 ^ (prefixWord ++ tailWord_1215150).sum := by decide
  have hdescent : baseEnd_1215150 < baseStart_1215150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215157 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_1215157 : Nat := 118140960795 + 1215157 * 2 ^ 59
def prefixEnd_1215157 : Nat := 4983230072969 + 3 ^ 40 * 1215157 * 2
def baseEnd_1215157 : Nat := 623959611675607426349101

theorem tailTrace_1215157 : CollatzResearch.WordTrace tailWord_1215157 prefixEnd_1215157 623959611675607426349101 := by
  unfold tailWord_1215157
  simp only [CollatzResearch.WordTrace]
  refine ⟨44320416858701196138219725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29546944572467464092146483 44320416858701196138219725)
  ·
    refine ⟨16620156322012948551832397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44320416858701196138219725 16620156322012948551832397)
    ·
      refine ⟨6232558620754855706937149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16620156322012948551832397 6232558620754855706937149)
      ·
        refine ⟨2337209482783070890101431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6232558620754855706937149 2337209482783070890101431)
        ·
          refine ⟨3505814224174606335152147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337209482783070890101431 3505814224174606335152147)
          ·
            refine ⟨5258721336261909502728221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3505814224174606335152147 5258721336261909502728221)
            ·
              refine ⟨1972020501098216063523083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5258721336261909502728221 1972020501098216063523083)
              ·
                refine ⟨2958030751647324095284625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1972020501098216063523083 2958030751647324095284625)
                ·
                  refine ⟨2218523063735493071463469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2958030751647324095284625 2218523063735493071463469)
                  ·
                    refine ⟨831946148900809901798801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218523063735493071463469 831946148900809901798801)
                    ·
                      refine ⟨623959611675607426349101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 831946148900809901798801 623959611675607426349101)
                      ·
                        rfl

theorem cell23_1215157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_1215157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215157 prefixEnd_1215157 := by exact prefixLift 1215157
  have htrace : WordTrace (prefixWord ++ tailWord_1215157) baseStart_1215157 baseEnd_1215157 := by
    simpa [prefixWord, tailWord_1215157, baseEnd_1215157] using wordTrace_append hprefix tailTrace_1215157
  have hstable : (prefixWord ++ tailWord_1215157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215157).length < 2 ^ (prefixWord ++ tailWord_1215157).sum := by decide
  have hdescent : baseEnd_1215157 < baseStart_1215157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215176 : List Nat := [2, 1, 3, 1, 2, 4, 10]
def baseStart_1215176 : Nat := 118140960795 + 1215176 * 2 ^ 59
def prefixEnd_1215176 : Nat := 4983230072969 + 3 ^ 40 * 1215176 * 2
def baseEnd_1215176 : Nat := 7703325528494356197673

theorem tailTrace_1215176 : CollatzResearch.WordTrace tailWord_1215176 prefixEnd_1215176 7703325528494356197673 := by
  unfold tailWord_1215176
  simp only [CollatzResearch.WordTrace]
  refine ⟨22160554922816181191580691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29547406563754908255440921 22160554922816181191580691)
  ·
    refine ⟨33240832384224271787371037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22160554922816181191580691 33240832384224271787371037)
    ·
      refine ⟨12465312144084101920264139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33240832384224271787371037 12465312144084101920264139)
      ·
        refine ⟨18697968216126152880396209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12465312144084101920264139 18697968216126152880396209)
        ·
          refine ⟨14023476162094614660297157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18697968216126152880396209 14023476162094614660297157)
          ·
            refine ⟨2629401780392740248805717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14023476162094614660297157 2629401780392740248805717)
            ·
              refine ⟨7703325528494356197673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2629401780392740248805717 7703325528494356197673)
              ·
                rfl

theorem cell23_1215176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 10].length) (baseStart_1215176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215176 prefixEnd_1215176 := by exact prefixLift 1215176
  have htrace : WordTrace (prefixWord ++ tailWord_1215176) baseStart_1215176 baseEnd_1215176 := by
    simpa [prefixWord, tailWord_1215176, baseEnd_1215176] using wordTrace_append hprefix tailTrace_1215176
  have hstable : (prefixWord ++ tailWord_1215176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215176).length < 2 ^ (prefixWord ++ tailWord_1215176).sum := by decide
  have hdescent : baseEnd_1215176 < baseStart_1215176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215180 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_1215180 : Nat := 118140960795 + 1215180 * 2 ^ 59
def prefixEnd_1215180 : Nat := 4983230072969 + 3 ^ 40 * 1215180 * 2
def baseEnd_1215180 : Nat := 207990473910220278787165

theorem tailTrace_1215180 : CollatzResearch.WordTrace tailWord_1215180 prefixEnd_1215180 207990473910220278787165 := by
  unfold tailWord_1215180
  simp only [CollatzResearch.WordTrace]
  refine ⟨22160627868808935533153497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29547503825078580710871329 22160627868808935533153497)
  ·
    refine ⟨16620470901606701649865123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22160627868808935533153497 16620470901606701649865123)
    ·
      refine ⟨24930706352410052474797685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16620470901606701649865123 24930706352410052474797685)
      ·
        refine ⟨2337253720538442419512283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24930706352410052474797685 2337253720538442419512283)
        ·
          refine ⟨3505880580807663629268425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337253720538442419512283 3505880580807663629268425)
          ·
            refine ⟨2629410435605747721951319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3505880580807663629268425 2629410435605747721951319)
            ·
              refine ⟨3944115653408621582926979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629410435605747721951319 3944115653408621582926979)
              ·
                refine ⟨5916173480112932374390469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944115653408621582926979 5916173480112932374390469)
                ·
                  refine ⟨1109282527521174820198213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5916173480112932374390469 1109282527521174820198213)
                  ·
                    refine ⟨207990473910220278787165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1109282527521174820198213 207990473910220278787165)
                    ·
                      rfl

theorem cell23_1215180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_1215180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215180 prefixEnd_1215180 := by exact prefixLift 1215180
  have htrace : WordTrace (prefixWord ++ tailWord_1215180) baseStart_1215180 baseEnd_1215180 := by
    simpa [prefixWord, tailWord_1215180, baseEnd_1215180] using wordTrace_append hprefix tailTrace_1215180
  have hstable : (prefixWord ++ tailWord_1215180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215180).length < 2 ^ (prefixWord ++ tailWord_1215180).sum := by decide
  have hdescent : baseEnd_1215180 < baseStart_1215180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215216 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_1215216 : Nat := 118140960795 + 1215216 * 2 ^ 59
def prefixEnd_1215216 : Nat := 4983230072969 + 3 ^ 40 * 1215216 * 2
def baseEnd_1215216 : Nat := 623989907034222695511329

theorem tailTrace_1215216 : CollatzResearch.WordTrace tailWord_1215216 prefixEnd_1215216 623989907034222695511329 := by
  unfold tailWord_1215216
  simp only [CollatzResearch.WordTrace]
  refine ⟨22161284382743724607308751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29548379176991632809745001 22161284382743724607308751)
  ·
    refine ⟨33241926574115586910963127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22161284382743724607308751 33241926574115586910963127)
    ·
      refine ⟨49862889861173380366444691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33241926574115586910963127 49862889861173380366444691)
      ·
        refine ⟨74794334791760070549667037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49862889861173380366444691 74794334791760070549667037)
        ·
          refine ⟨28047875546910026456125139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74794334791760070549667037 28047875546910026456125139)
          ·
            refine ⟨42071813320365039684187709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28047875546910026456125139 42071813320365039684187709)
            ·
              refine ⟨15776929995136889881570391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42071813320365039684187709 15776929995136889881570391)
              ·
                refine ⟨23665394992705334822355587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15776929995136889881570391 23665394992705334822355587)
                ·
                  refine ⟨35498092489058002233533381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23665394992705334822355587 35498092489058002233533381)
                  ·
                    refine ⟨6655892341698375418787509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35498092489058002233533381 6655892341698375418787509)
                    ·
                      refine ⟨623989907034222695511329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6655892341698375418787509 623989907034222695511329)
                      ·
                        rfl

theorem cell23_1215216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_1215216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215216 prefixEnd_1215216 := by exact prefixLift 1215216
  have htrace : WordTrace (prefixWord ++ tailWord_1215216) baseStart_1215216 baseEnd_1215216 := by
    simpa [prefixWord, tailWord_1215216, baseEnd_1215216] using wordTrace_append hprefix tailTrace_1215216
  have hstable : (prefixWord ++ tailWord_1215216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215216).length < 2 ^ (prefixWord ++ tailWord_1215216).sum := by decide
  have hdescent : baseEnd_1215216 < baseStart_1215216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215263 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1215263 : Nat := 118140960795 + 1215263 * 2 ^ 59
def prefixEnd_1215263 : Nat := 4983230072969 + 3 ^ 40 * 1215263 * 2
def baseEnd_1215263 : Nat := 624014040624984011623613

theorem tailTrace_1215263 : CollatzResearch.WordTrace tailWord_1215263 prefixEnd_1215263 624014040624984011623613 := by
  unfold tailWord_1215263
  simp only [CollatzResearch.WordTrace]
  refine ⟨44324282996317176241578443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29549521997544784161052295 44324282996317176241578443)
  ·
    refine ⟨66486424494475764362367665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44324282996317176241578443 66486424494475764362367665)
    ·
      refine ⟨49864818370856823271775749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66486424494475764362367665 49864818370856823271775749)
      ·
        refine ⟨9349653444535654363457953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49864818370856823271775749 9349653444535654363457953)
        ·
          refine ⟨7012240083401740772593465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9349653444535654363457953 7012240083401740772593465)
          ·
            refine ⟨5259180062551305579445099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7012240083401740772593465 5259180062551305579445099)
            ·
              refine ⟨7888770093826958369167649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259180062551305579445099 7888770093826958369167649)
              ·
                refine ⟨5916577570370218776875737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7888770093826958369167649 5916577570370218776875737)
                ·
                  refine ⟨4437433177777664082656803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5916577570370218776875737 4437433177777664082656803)
                  ·
                    refine ⟨6656149766666496123985205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4437433177777664082656803 6656149766666496123985205)
                    ·
                      refine ⟨624014040624984011623613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6656149766666496123985205 624014040624984011623613)
                      ·
                        rfl

theorem cell23_1215263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1215263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215263 prefixEnd_1215263 := by exact prefixLift 1215263
  have htrace : WordTrace (prefixWord ++ tailWord_1215263) baseStart_1215263 baseEnd_1215263 := by
    simpa [prefixWord, tailWord_1215263, baseEnd_1215263] using wordTrace_append hprefix tailTrace_1215263
  have hstable : (prefixWord ++ tailWord_1215263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215263).length < 2 ^ (prefixWord ++ tailWord_1215263).sum := by decide
  have hdescent : baseEnd_1215263 < baseStart_1215263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215264 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 1, 3, 2]
def baseStart_1215264 : Nat := 118140960795 + 1215264 * 2 ^ 59
def prefixEnd_1215264 : Nat := 4983230072969 + 3 ^ 40 * 1215264 * 2
def baseEnd_1215264 : Nat := 624014554105638507711109

theorem tailTrace_1215264 : CollatzResearch.WordTrace tailWord_1215264 prefixEnd_1215264 624014554105638507711109 := by
  unfold tailWord_1215264
  simp only [CollatzResearch.WordTrace]
  refine ⟨22162159734656776706182423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29549546312875702274909897 22162159734656776706182423)
  ·
    refine ⟨33243239601985165059273635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22162159734656776706182423 33243239601985165059273635)
    ·
      refine ⟨49864859402977747588910453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33243239601985165059273635 49864859402977747588910453)
      ·
        refine ⟨4674830569029163836460355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49864859402977747588910453 4674830569029163836460355)
        ·
          refine ⟨7012245853543745754690533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4674830569029163836460355 7012245853543745754690533)
          ·
            refine ⟨1314796097539452329004475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7012245853543745754690533 1314796097539452329004475)
            ·
              refine ⟨1972194146309178493506713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314796097539452329004475 1972194146309178493506713)
              ·
                refine ⟨1479145609731883870130035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1972194146309178493506713 1479145609731883870130035)
                ·
                  refine ⟨2218718414597825805195053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479145609731883870130035 2218718414597825805195053)
                  ·
                    refine ⟨832019405474184676948145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2218718414597825805195053 832019405474184676948145)
                    ·
                      refine ⟨624014554105638507711109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832019405474184676948145 624014554105638507711109)
                      ·
                        rfl

theorem cell23_1215264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_1215264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215264 prefixEnd_1215264 := by exact prefixLift 1215264
  have htrace : WordTrace (prefixWord ++ tailWord_1215264) baseStart_1215264 baseEnd_1215264 := by
    simpa [prefixWord, tailWord_1215264, baseEnd_1215264] using wordTrace_append hprefix tailTrace_1215264
  have hstable : (prefixWord ++ tailWord_1215264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215264).length < 2 ^ (prefixWord ++ tailWord_1215264).sum := by decide
  have hdescent : baseEnd_1215264 < baseStart_1215264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215363 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 6]
def baseStart_1215363 : Nat := 118140960795 + 1215363 * 2 ^ 59
def prefixEnd_1215363 : Nat := 4983230072969 + 3 ^ 40 * 1215363 * 2
def baseEnd_1215363 : Nat := 624065388690433620373153

theorem tailTrace_1215363 : CollatzResearch.WordTrace tailWord_1215363 prefixEnd_1215363 624065388690433620373153 := by
  unfold tailWord_1215363
  simp only [CollatzResearch.WordTrace]
  refine ⟨44327930295954893320218743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29551953530636595546812495 44327930295954893320218743)
  ·
    refine ⟨66491895443932339980328115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44327930295954893320218743 66491895443932339980328115)
    ·
      refine ⟨99737843165898509970492173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66491895443932339980328115 99737843165898509970492173)
      ·
        refine ⟨37401691187211941238934565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99737843165898509970492173 37401691187211941238934565)
        ·
          refine ⟨7012817097602238982300231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37401691187211941238934565 7012817097602238982300231)
          ·
            refine ⟨10519225646403358473450347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7012817097602238982300231 10519225646403358473450347)
            ·
              refine ⟨15778838469605037710175521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10519225646403358473450347 15778838469605037710175521)
              ·
                refine ⟨11834128852203778282631641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15778838469605037710175521 11834128852203778282631641)
                ·
                  refine ⟨8875596639152833711973731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11834128852203778282631641 8875596639152833711973731)
                  ·
                    refine ⟨13313394958729250567960597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8875596639152833711973731 13313394958729250567960597)
                    ·
                      refine ⟨624065388690433620373153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13313394958729250567960597 624065388690433620373153)
                      ·
                        rfl

theorem cell23_1215363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_1215363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215363 prefixEnd_1215363 := by exact prefixLift 1215363
  have htrace : WordTrace (prefixWord ++ tailWord_1215363) baseStart_1215363 baseEnd_1215363 := by
    simpa [prefixWord, tailWord_1215363, baseEnd_1215363] using wordTrace_append hprefix tailTrace_1215363
  have hstable : (prefixWord ++ tailWord_1215363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215363).length < 2 ^ (prefixWord ++ tailWord_1215363).sum := by decide
  have hdescent : baseEnd_1215363 < baseStart_1215363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215367 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_1215367 : Nat := 118140960795 + 1215367 * 2 ^ 59
def prefixEnd_1215367 : Nat := 4983230072969 + 3 ^ 40 * 1215367 * 2
def baseEnd_1215367 : Nat := 624067442613051604723135

theorem tailTrace_1215367 : CollatzResearch.WordTrace tailWord_1215367 prefixEnd_1215367 624067442613051604723135 := by
  unfold tailWord_1215367
  simp only [CollatzResearch.WordTrace]
  refine ⟨44328076187940402003364355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29552050791960268002242903 44328076187940402003364355)
  ·
    refine ⟨66492114281910603005046533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44328076187940402003364355 66492114281910603005046533)
    ·
      refine ⟨12467271427858238063446225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66492114281910603005046533 12467271427858238063446225)
      ·
        refine ⟨9350453570893678547584669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12467271427858238063446225 9350453570893678547584669)
        ·
          refine ⟨3506420089085129455344251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9350453570893678547584669 3506420089085129455344251)
          ·
            refine ⟨5259630133627694183016377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506420089085129455344251 5259630133627694183016377)
            ·
              refine ⟨3944722600220770637262283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5259630133627694183016377 3944722600220770637262283)
              ·
                refine ⟨5917083900331155955893425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3944722600220770637262283 5917083900331155955893425)
                ·
                  refine ⟨4437812925248366966920069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5917083900331155955893425 4437812925248366966920069)
                  ·
                    refine ⟨832089923484068806297513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4437812925248366966920069 832089923484068806297513)
                    ·
                      refine ⟨624067442613051604723135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832089923484068806297513 624067442613051604723135)
                      ·
                        rfl

theorem cell23_1215367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_1215367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215367 prefixEnd_1215367 := by exact prefixLift 1215367
  have htrace : WordTrace (prefixWord ++ tailWord_1215367) baseStart_1215367 baseEnd_1215367 := by
    simpa [prefixWord, tailWord_1215367, baseEnd_1215367] using wordTrace_append hprefix tailTrace_1215367
  have hstable : (prefixWord ++ tailWord_1215367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215367).length < 2 ^ (prefixWord ++ tailWord_1215367).sum := by decide
  have hdescent : baseEnd_1215367 < baseStart_1215367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215380 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_1215380 : Nat := 118140960795 + 1215380 * 2 ^ 59
def prefixEnd_1215380 : Nat := 4983230072969 + 3 ^ 40 * 1215380 * 2
def baseEnd_1215380 : Nat := 624074117861560053860575

theorem tailTrace_1215380 : CollatzResearch.WordTrace tailWord_1215380 prefixEnd_1215380 624074117861560053860575 := by
  unfold tailWord_1215380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22164275168446652611793797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29552366891262203482391729 22164275168446652611793797)
  ·
    refine ⟨4155801594083747364711337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22164275168446652611793797 4155801594083747364711337)
    ·
      refine ⟨3116851195562810523533503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4155801594083747364711337 3116851195562810523533503)
      ·
        refine ⟨4675276793344215785300255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3116851195562810523533503 4675276793344215785300255)
        ·
          refine ⟨7012915190016323677950383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4675276793344215785300255 7012915190016323677950383)
          ·
            refine ⟨10519372785024485516925575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7012915190016323677950383 10519372785024485516925575)
            ·
              refine ⟨15779059177536728275388363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10519372785024485516925575 15779059177536728275388363)
              ·
                refine ⟨23668588766305092413082545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15779059177536728275388363 23668588766305092413082545)
                ·
                  refine ⟨17751441574728819309811909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23668588766305092413082545 17751441574728819309811909)
                  ·
                    refine ⟨3328395295261653620589733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17751441574728819309811909 3328395295261653620589733)
                    ·
                      refine ⟨624074117861560053860575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3328395295261653620589733 624074117861560053860575)
                      ·
                        rfl

theorem cell23_1215380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_1215380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215380 prefixEnd_1215380 := by exact prefixLift 1215380
  have htrace : WordTrace (prefixWord ++ tailWord_1215380) baseStart_1215380 baseEnd_1215380 := by
    simpa [prefixWord, tailWord_1215380, baseEnd_1215380] using wordTrace_append hprefix tailTrace_1215380
  have hstable : (prefixWord ++ tailWord_1215380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215380).length < 2 ^ (prefixWord ++ tailWord_1215380).sum := by decide
  have hdescent : baseEnd_1215380 < baseStart_1215380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215444 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_1215444 : Nat := 118140960795 + 1215444 * 2 ^ 59
def prefixEnd_1215444 : Nat := 4983230072969 + 3 ^ 40 * 1215444 * 2
def baseEnd_1215444 : Nat := 624106980623447803460281

theorem tailTrace_1215444 : CollatzResearch.WordTrace tailWord_1215444 prefixEnd_1215444 624106980623447803460281 := by
  unfold tailWord_1215444
  simp only [CollatzResearch.WordTrace]
  refine ⟨22165442304330722076958693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29553923072440962769278257 22165442304330722076958693)
  ·
    refine ⟨4156020432062010389429755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22165442304330722076958693 4156020432062010389429755)
    ·
      refine ⟨6234030648093015584144633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4156020432062010389429755 6234030648093015584144633)
      ·
        refine ⟨4675522986069761688108475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6234030648093015584144633 4675522986069761688108475)
        ·
          refine ⟨7013284479104642532162713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4675522986069761688108475 7013284479104642532162713)
          ·
            refine ⟨5259963359328481899122035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7013284479104642532162713 5259963359328481899122035)
            ·
              refine ⟨7889945038992722848683053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259963359328481899122035 7889945038992722848683053)
              ·
                refine ⟨2958729389622271068256145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7889945038992722848683053 2958729389622271068256145)
                ·
                  refine ⟨2219047042216703301192109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2958729389622271068256145 2219047042216703301192109)
                  ·
                    refine ⟨832142640831263737947041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2219047042216703301192109 832142640831263737947041)
                    ·
                      refine ⟨624106980623447803460281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832142640831263737947041 624106980623447803460281)
                      ·
                        rfl

theorem cell23_1215444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_1215444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215444 prefixEnd_1215444 := by exact prefixLift 1215444
  have htrace : WordTrace (prefixWord ++ tailWord_1215444) baseStart_1215444 baseEnd_1215444 := by
    simpa [prefixWord, tailWord_1215444, baseEnd_1215444] using wordTrace_append hprefix tailTrace_1215444
  have hstable : (prefixWord ++ tailWord_1215444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215444).length < 2 ^ (prefixWord ++ tailWord_1215444).sum := by decide
  have hdescent : baseEnd_1215444 < baseStart_1215444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215450 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_1215450 : Nat := 118140960795 + 1215450 * 2 ^ 59
def prefixEnd_1215450 : Nat := 4983230072969 + 3 ^ 40 * 1215450 * 2
def baseEnd_1215450 : Nat := 208036687169124926661751

theorem tailTrace_1215450 : CollatzResearch.WordTrace tailWord_1215450 prefixEnd_1215450 208036687169124926661751 := by
  unfold tailWord_1215450
  simp only [CollatzResearch.WordTrace]
  refine ⟨11082775861659926794658951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29554068964426471452423869 11082775861659926794658951)
  ·
    refine ⟨16624163792489890191988427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11082775861659926794658951 16624163792489890191988427)
    ·
      refine ⟨24936245688734835287982641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16624163792489890191988427 24936245688734835287982641)
      ·
        refine ⟨18702184266551126465986981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24936245688734835287982641 18702184266551126465986981)
        ·
          refine ⟨3506659549978336212372559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18702184266551126465986981 3506659549978336212372559)
          ·
            refine ⟨5259989324967504318558839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506659549978336212372559 5259989324967504318558839)
            ·
              refine ⟨7889983987451256477838259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5259989324967504318558839 7889983987451256477838259)
              ·
                refine ⟨11834975981176884716757389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7889983987451256477838259 11834975981176884716757389)
                ·
                  refine ⟨4438115992941331768784021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11834975981176884716757389 4438115992941331768784021)
                  ·
                    refine ⟨208036687169124926661751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4438115992941331768784021 208036687169124926661751)
                    ·
                      rfl

theorem cell23_1215450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_1215450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215450 prefixEnd_1215450 := by exact prefixLift 1215450
  have htrace : WordTrace (prefixWord ++ tailWord_1215450) baseStart_1215450 baseEnd_1215450 := by
    simpa [prefixWord, tailWord_1215450, baseEnd_1215450] using wordTrace_append hprefix tailTrace_1215450
  have hstable : (prefixWord ++ tailWord_1215450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215450).length < 2 ^ (prefixWord ++ tailWord_1215450).sum := by decide
  have hdescent : baseEnd_1215450 < baseStart_1215450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215460 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_1215460 : Nat := 118140960795 + 1215460 * 2 ^ 59
def prefixEnd_1215460 : Nat := 4983230072969 + 3 ^ 40 * 1215460 * 2
def baseEnd_1215460 : Nat := 624115196313919740860207

theorem tailTrace_1215460 : CollatzResearch.WordTrace tailWord_1215460 prefixEnd_1215460 624115196313919740860207 := by
  unfold tailWord_1215460
  simp only [CollatzResearch.WordTrace]
  refine ⟨22165734088301739443249917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29554312117735652590999889 22165734088301739443249917)
  ·
    refine ⟨8312150283113152291218719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22165734088301739443249917 8312150283113152291218719)
    ·
      refine ⟨12468225424669728436828079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8312150283113152291218719 12468225424669728436828079)
      ·
        refine ⟨18702338137004592655242119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12468225424669728436828079 18702338137004592655242119)
        ·
          refine ⟨28053507205506888982863179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18702338137004592655242119 28053507205506888982863179)
          ·
            refine ⟨42080260808260333474294769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28053507205506888982863179 42080260808260333474294769)
            ·
              refine ⟨31560195606195250105721077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42080260808260333474294769 31560195606195250105721077)
              ·
                refine ⟨2958768338080804697411351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31560195606195250105721077 2958768338080804697411351)
                ·
                  refine ⟨4438152507121207046117027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2958768338080804697411351 4438152507121207046117027)
                  ·
                    refine ⟨6657228760681810569175541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4438152507121207046117027 6657228760681810569175541)
                    ·
                      refine ⟨624115196313919740860207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6657228760681810569175541 624115196313919740860207)
                      ·
                        rfl

theorem cell23_1215460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_1215460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215460 prefixEnd_1215460 := by exact prefixLift 1215460
  have htrace : WordTrace (prefixWord ++ tailWord_1215460) baseStart_1215460 baseEnd_1215460 := by
    simpa [prefixWord, tailWord_1215460, baseEnd_1215460] using wordTrace_append hprefix tailTrace_1215460
  have hstable : (prefixWord ++ tailWord_1215460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215460).length < 2 ^ (prefixWord ++ tailWord_1215460).sum := by decide
  have hdescent : baseEnd_1215460 < baseStart_1215460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215507 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 3]
def baseStart_1215507 : Nat := 118140960795 + 1215507 * 2 ^ 59
def prefixEnd_1215507 : Nat := 4983230072969 + 3 ^ 40 * 1215507 * 2
def baseEnd_1215507 : Nat := 624139329904681056972491

theorem tailTrace_1215507 : CollatzResearch.WordTrace tailWord_1215507 prefixEnd_1215507 624139329904681056972491 := by
  unfold tailWord_1215507
  simp only [CollatzResearch.WordTrace]
  refine ⟨44333182407433205913460775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29555454938288803942307183 44333182407433205913460775)
  ·
    refine ⟨66499773611149808870191163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44333182407433205913460775 66499773611149808870191163)
    ·
      refine ⟨99749660416724713305286745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66499773611149808870191163 99749660416724713305286745)
      ·
        refine ⟨74812245312543534978965059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99749660416724713305286745 74812245312543534978965059)
        ·
          refine ⟨112218367968815302468447589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74812245312543534978965059 112218367968815302468447589)
          ·
            refine ⟨21040943994152869212833923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112218367968815302468447589 21040943994152869212833923)
            ·
              refine ⟨31561415991229303819250885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21040943994152869212833923 31561415991229303819250885)
              ·
                refine ⟨5917765498355494466109541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31561415991229303819250885 5917765498355494466109541)
                ·
                  refine ⟨1109581030941655212395539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5917765498355494466109541 1109581030941655212395539)
                  ·
                    refine ⟨1664371546412482818593309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1109581030941655212395539 1664371546412482818593309)
                    ·
                      refine ⟨624139329904681056972491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1664371546412482818593309 624139329904681056972491)
                      ·
                        rfl

theorem cell23_1215507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 3].length) (baseStart_1215507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215507 prefixEnd_1215507 := by exact prefixLift 1215507
  have htrace : WordTrace (prefixWord ++ tailWord_1215507) baseStart_1215507 baseEnd_1215507 := by
    simpa [prefixWord, tailWord_1215507, baseEnd_1215507] using wordTrace_append hprefix tailTrace_1215507
  have hstable : (prefixWord ++ tailWord_1215507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215507).length < 2 ^ (prefixWord ++ tailWord_1215507).sum := by decide
  have hdescent : baseEnd_1215507 < baseStart_1215507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215511 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 1, 2, 3]
def baseStart_1215511 : Nat := 118140960795 + 1215511 * 2 ^ 59
def prefixEnd_1215511 : Nat := 4983230072969 + 3 ^ 40 * 1215511 * 2
def baseEnd_1215511 : Nat := 624141383827299041322473

theorem tailTrace_1215511 : CollatzResearch.WordTrace tailWord_1215511 prefixEnd_1215511 624141383827299041322473 := by
  unfold tailWord_1215511
  simp only [CollatzResearch.WordTrace]
  refine ⟨44333328299418714596606387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29555552199612476397737591 44333328299418714596606387)
  ·
    refine ⟨66499992449128071894909581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44333328299418714596606387 66499992449128071894909581)
    ·
      refine ⟨24937497168423026960591093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66499992449128071894909581 24937497168423026960591093)
      ·
        refine ⟨2337890359539658777555415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24937497168423026960591093 2337890359539658777555415)
        ·
          refine ⟨3506835539309488166333123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337890359539658777555415 3506835539309488166333123)
          ·
            refine ⟨5260253308964232249499685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3506835539309488166333123 5260253308964232249499685)
            ·
              refine ⟨986297495430793546781191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5260253308964232249499685 986297495430793546781191)
              ·
                refine ⟨1479446243146190320171787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986297495430793546781191 1479446243146190320171787)
                ·
                  refine ⟨2219169364719285480257681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479446243146190320171787 2219169364719285480257681)
                  ·
                    refine ⟨1664377023539464110193261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2219169364719285480257681 1664377023539464110193261)
                    ·
                      refine ⟨624141383827299041322473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1664377023539464110193261 624141383827299041322473)
                      ·
                        rfl

theorem cell23_1215511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_1215511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215511 prefixEnd_1215511 := by exact prefixLift 1215511
  have htrace : WordTrace (prefixWord ++ tailWord_1215511) baseStart_1215511 baseEnd_1215511 := by
    simpa [prefixWord, tailWord_1215511, baseEnd_1215511] using wordTrace_append hprefix tailTrace_1215511
  have hstable : (prefixWord ++ tailWord_1215511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215511).length < 2 ^ (prefixWord ++ tailWord_1215511).sum := by decide
  have hdescent : baseEnd_1215511 < baseStart_1215511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215592 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1215592 : Nat := 118140960795 + 1215592 * 2 ^ 59
def prefixEnd_1215592 : Nat := 4983230072969 + 3 ^ 40 * 1215592 * 2
def baseEnd_1215592 : Nat := 624182975760313224409601

theorem tailTrace_1215592 : CollatzResearch.WordTrace tailWord_1215592 prefixEnd_1215592 624182975760313224409601 := by
  unfold tailWord_1215592
  simp only [CollatzResearch.WordTrace]
  refine ⟨22168141306062632715152515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29557521741416843620203353 22168141306062632715152515)
  ·
    refine ⟨33252211959093949072728773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22168141306062632715152515 33252211959093949072728773)
    ·
      refine ⟨6234789742330115451136645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33252211959093949072728773 6234789742330115451136645)
      ·
        refine ⟨1169023076686896647088121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6234789742330115451136645 1169023076686896647088121)
        ·
          refine ⟨876767307515172485316091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1169023076686896647088121 876767307515172485316091)
          ·
            refine ⟨1315150961272758727974137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876767307515172485316091 1315150961272758727974137)
            ·
              refine ⟨986363220954569045980603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315150961272758727974137 986363220954569045980603)
              ·
                refine ⟨1479544831431853568970905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986363220954569045980603 1479544831431853568970905)
                ·
                  refine ⟨1109658623573890176728179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1479544831431853568970905 1109658623573890176728179)
                  ·
                    refine ⟨1664487935360835265092269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1109658623573890176728179 1664487935360835265092269)
                    ·
                      refine ⟨624182975760313224409601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1664487935360835265092269 624182975760313224409601)
                      ·
                        rfl

theorem cell23_1215592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1215592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215592 prefixEnd_1215592 := by exact prefixLift 1215592
  have htrace : WordTrace (prefixWord ++ tailWord_1215592) baseStart_1215592 baseEnd_1215592 := by
    simpa [prefixWord, tailWord_1215592, baseEnd_1215592] using wordTrace_append hprefix tailTrace_1215592
  have hstable : (prefixWord ++ tailWord_1215592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215592).length < 2 ^ (prefixWord ++ tailWord_1215592).sum := by decide
  have hdescent : baseEnd_1215592 < baseStart_1215592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215598 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_1215598 : Nat := 118140960795 + 1215598 * 2 ^ 59
def prefixEnd_1215598 : Nat := 4983230072969 + 3 ^ 40 * 1215598 * 2
def baseEnd_1215598 : Nat := 624186056644240200934573

theorem tailTrace_1215598 : CollatzResearch.WordTrace tailWord_1215598 prefixEnd_1215598 624186056644240200934573 := by
  unfold tailWord_1215598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5542062681262941056877931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29557667633402352303348965 5542062681262941056877931)
  ·
    refine ⟨8313094021894411585316897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5542062681262941056877931 8313094021894411585316897)
    ·
      refine ⟨6234820516420808688987673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8313094021894411585316897 6234820516420808688987673)
      ·
        refine ⟨4676115387315606516740755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6234820516420808688987673 4676115387315606516740755)
        ·
          refine ⟨7014173080973409775111133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4676115387315606516740755 7014173080973409775111133)
          ·
            refine ⟨2630314905365028665666675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7014173080973409775111133 2630314905365028665666675)
            ·
              refine ⟨3945472358047542998500013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630314905365028665666675 3945472358047542998500013)
              ·
                refine ⟨1479552134267828624437505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3945472358047542998500013 1479552134267828624437505)
                ·
                  refine ⟨1109664100700871468328129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1479552134267828624437505 1109664100700871468328129)
                  ·
                    refine ⟨832248075525653601246097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1109664100700871468328129 832248075525653601246097)
                    ·
                      refine ⟨624186056644240200934573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832248075525653601246097 624186056644240200934573)
                      ·
                        rfl

theorem cell23_1215598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_1215598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215598 prefixEnd_1215598 := by exact prefixLift 1215598
  have htrace : WordTrace (prefixWord ++ tailWord_1215598) baseStart_1215598 baseEnd_1215598 := by
    simpa [prefixWord, tailWord_1215598, baseEnd_1215598] using wordTrace_append hprefix tailTrace_1215598
  have hstable : (prefixWord ++ tailWord_1215598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215598).length < 2 ^ (prefixWord ++ tailWord_1215598).sum := by decide
  have hdescent : baseEnd_1215598 < baseStart_1215598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215634 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1215634 : Nat := 118140960795 + 1215634 * 2 ^ 59
def prefixEnd_1215634 : Nat := 4983230072969 + 3 ^ 40 * 1215634 * 2
def baseEnd_1215634 : Nat := 208068180649267353361469

theorem tailTrace_1215634 : CollatzResearch.WordTrace tailWord_1215634 prefixEnd_1215634 208068180649267353361469 := by
  unfold tailWord_1215634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11084453619493276650833489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29558542985315404402222637 11084453619493276650833489)
  ·
    refine ⟨8313340214619957488125117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11084453619493276650833489 8313340214619957488125117)
    ·
      refine ⟨3117502580482484058046919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8313340214619957488125117 3117502580482484058046919)
      ·
        refine ⟨4676253870723726087070379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3117502580482484058046919 4676253870723726087070379)
        ·
          refine ⟨7014380806085589130605569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4676253870723726087070379 7014380806085589130605569)
          ·
            refine ⟨5260785604564191847954177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7014380806085589130605569 5260785604564191847954177)
            ·
              refine ⟨3945589203423143885965633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5260785604564191847954177 3945589203423143885965633)
              ·
                refine ⟨2959191902567357914474225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945589203423143885965633 2959191902567357914474225)
                ·
                  refine ⟨2219393926925518435855669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2959191902567357914474225 2219393926925518435855669)
                  ·
                    refine ⟨208068180649267353361469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2219393926925518435855669 208068180649267353361469)
                    ·
                      rfl

theorem cell23_1215634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1215634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215634 prefixEnd_1215634 := by exact prefixLift 1215634
  have htrace : WordTrace (prefixWord ++ tailWord_1215634) baseStart_1215634 baseEnd_1215634 := by
    simpa [prefixWord, tailWord_1215634, baseEnd_1215634] using wordTrace_append hprefix tailTrace_1215634
  have hstable : (prefixWord ++ tailWord_1215634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215634).length < 2 ^ (prefixWord ++ tailWord_1215634).sum := by decide
  have hdescent : baseEnd_1215634 < baseStart_1215634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215637 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_1215637 : Nat := 118140960795 + 1215637 * 2 ^ 59
def prefixEnd_1215637 : Nat := 4983230072969 + 3 ^ 40 * 1215637 * 2
def baseEnd_1215637 : Nat := 624206082389765548346893

theorem tailTrace_1215637 : CollatzResearch.WordTrace tailWord_1215637 prefixEnd_1215637 624206082389765548346893 := by
  unfold tailWord_1215637
  simp only [CollatzResearch.WordTrace]
  refine ⟨44337923896962238115693165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29558615931308158743795443 44337923896962238115693165)
  ·
    refine ⟨16626721461360839293384937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44337923896962238115693165 16626721461360839293384937)
    ·
      refine ⟨12470041096020629470038703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16626721461360839293384937 12470041096020629470038703)
      ·
        refine ⟨18705061644030944205058055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12470041096020629470038703 18705061644030944205058055)
        ·
          refine ⟨28057592466046416307587083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18705061644030944205058055 28057592466046416307587083)
          ·
            refine ⟨42086388699069624461380625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28057592466046416307587083 42086388699069624461380625)
            ·
              refine ⟨31564791524302218346035469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42086388699069624461380625 31564791524302218346035469)
              ·
                refine ⟨11836796821613331879763301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31564791524302218346035469 11836796821613331879763301)
                ·
                  refine ⟨2219399404052499727455619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11836796821613331879763301 2219399404052499727455619)
                  ·
                    refine ⟨3329099106078749591183429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2219399404052499727455619 3329099106078749591183429)
                    ·
                      refine ⟨624206082389765548346893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3329099106078749591183429 624206082389765548346893)
                      ·
                        rfl

theorem cell23_1215637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_1215637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215637 prefixEnd_1215637 := by exact prefixLift 1215637
  have htrace : WordTrace (prefixWord ++ tailWord_1215637) baseStart_1215637 baseEnd_1215637 := by
    simpa [prefixWord, tailWord_1215637, baseEnd_1215637] using wordTrace_append hprefix tailTrace_1215637
  have hstable : (prefixWord ++ tailWord_1215637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215637).length < 2 ^ (prefixWord ++ tailWord_1215637).sum := by decide
  have hdescent : baseEnd_1215637 < baseStart_1215637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215687 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_1215687 : Nat := 118140960795 + 1215687 * 2 ^ 59
def prefixEnd_1215687 : Nat := 4983230072969 + 3 ^ 40 * 1215687 * 2
def baseEnd_1215687 : Nat := 624231756422490352721663

theorem tailTrace_1215687 : CollatzResearch.WordTrace tailWord_1215687 prefixEnd_1215687 624231756422490352721663 := by
  unfold tailWord_1215687
  simp only [CollatzResearch.WordTrace]
  refine ⟨44339747546781096655013315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29559831697854064436675543 44339747546781096655013315)
  ·
    refine ⟨66509621320171644982519973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44339747546781096655013315 66509621320171644982519973)
    ·
      refine ⟨12470553997532183434222495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66509621320171644982519973 12470553997532183434222495)
      ·
        refine ⟨18705830996298275151333743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12470553997532183434222495 18705830996298275151333743)
        ·
          refine ⟨28058746494447412727000615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18705830996298275151333743 28058746494447412727000615)
          ·
            refine ⟨42088119741671119090500923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28058746494447412727000615 42088119741671119090500923)
            ·
              refine ⟨63132179612506678635751385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42088119741671119090500923 63132179612506678635751385)
              ·
                refine ⟨47349134709380008976813539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63132179612506678635751385 47349134709380008976813539)
                ·
                  refine ⟨71023702064070013465220309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47349134709380008976813539 71023702064070013465220309)
                  ·
                    refine ⟨1664618017126640940591101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 71023702064070013465220309 1664618017126640940591101)
                    ·
                      refine ⟨624231756422490352721663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1664618017126640940591101 624231756422490352721663)
                      ·
                        rfl

theorem cell23_1215687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_1215687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215687 prefixEnd_1215687 := by exact prefixLift 1215687
  have htrace : WordTrace (prefixWord ++ tailWord_1215687) baseStart_1215687 baseEnd_1215687 := by
    simpa [prefixWord, tailWord_1215687, baseEnd_1215687] using wordTrace_append hprefix tailTrace_1215687
  have hstable : (prefixWord ++ tailWord_1215687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215687).length < 2 ^ (prefixWord ++ tailWord_1215687).sum := by decide
  have hdescent : baseEnd_1215687 < baseStart_1215687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215694 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_1215694 : Nat := 118140960795 + 1215694 * 2 ^ 59
def prefixEnd_1215694 : Nat := 4983230072969 + 3 ^ 40 * 1215694 * 2
def baseEnd_1215694 : Nat := 69359483420785758370459

theorem tailTrace_1215694 : CollatzResearch.WordTrace tailWord_1215694 prefixEnd_1215694 69359483420785758370459 := by
  unfold tailWord_1215694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5542500357219467106314767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29560001905170491233678757 5542500357219467106314767)
  ·
    refine ⟨8313750535829200659472151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5542500357219467106314767 8313750535829200659472151)
    ·
      refine ⟨12470625803743800989208227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8313750535829200659472151 12470625803743800989208227)
      ·
        refine ⟨18705938705615701483812341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12470625803743800989208227 18705938705615701483812341)
        ·
          refine ⟨1753681753651472014107407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18705938705615701483812341 1753681753651472014107407)
          ·
            refine ⟨2630522630477208021161111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753681753651472014107407 2630522630477208021161111)
            ·
              refine ⟨3945783945715812031741667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630522630477208021161111 3945783945715812031741667)
              ·
                refine ⟨5918675918573718047612501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3945783945715812031741667 5918675918573718047612501)
                ·
                  refine ⟨69359483420785758370459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5918675918573718047612501 69359483420785758370459)
                  ·
                    rfl

theorem cell23_1215694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_1215694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215694 prefixEnd_1215694 := by exact prefixLift 1215694
  have htrace : WordTrace (prefixWord ++ tailWord_1215694) baseStart_1215694 baseEnd_1215694 := by
    simpa [prefixWord, tailWord_1215694, baseEnd_1215694] using wordTrace_append hprefix tailTrace_1215694
  have hstable : (prefixWord ++ tailWord_1215694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215694).length < 2 ^ (prefixWord ++ tailWord_1215694).sum := by decide
  have hdescent : baseEnd_1215694 < baseStart_1215694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215724 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_1215724 : Nat := 118140960795 + 1215724 * 2 ^ 59
def prefixEnd_1215724 : Nat := 4983230072969 + 3 ^ 40 * 1215724 * 2
def baseEnd_1215724 : Nat := 208083585068902235986331

theorem tailTrace_1215724 : CollatzResearch.WordTrace tailWord_1215724 prefixEnd_1215724 208083585068902235986331 := by
  unfold tailWord_1215724
  simp only [CollatzResearch.WordTrace]
  refine ⟨22170548523823525987055113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29560731365098034649406817 22170548523823525987055113)
  ·
    refine ⟨16627911392867644490291335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22170548523823525987055113 16627911392867644490291335)
    ·
      refine ⟨24941867089301466735437003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16627911392867644490291335 24941867089301466735437003)
      ·
        refine ⟨37412800633952200103155505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24941867089301466735437003 37412800633952200103155505)
        ·
          refine ⟨28059600475464150077366629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37412800633952200103155505 28059600475464150077366629)
          ·
            refine ⟨5261175089149528139506243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28059600475464150077366629 5261175089149528139506243)
            ·
              refine ⟨7891762633724292209259365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5261175089149528139506243 7891762633724292209259365)
              ·
                refine ⟨1479705493823304789236131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7891762633724292209259365 1479705493823304789236131)
                ·
                  refine ⟨2219558240734957183854197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1479705493823304789236131 2219558240734957183854197)
                  ·
                    refine ⟨208083585068902235986331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2219558240734957183854197 208083585068902235986331)
                    ·
                      rfl

theorem cell23_1215724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_1215724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215724 prefixEnd_1215724 := by exact prefixLift 1215724
  have htrace : WordTrace (prefixWord ++ tailWord_1215724) baseStart_1215724 baseEnd_1215724 := by
    simpa [prefixWord, tailWord_1215724, baseEnd_1215724] using wordTrace_append hprefix tailTrace_1215724
  have hstable : (prefixWord ++ tailWord_1215724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215724).length < 2 ^ (prefixWord ++ tailWord_1215724).sum := by decide
  have hdescent : baseEnd_1215724 < baseStart_1215724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215737 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 3, 6]
def baseStart_1215737 : Nat := 118140960795 + 1215737 * 2 ^ 59
def prefixEnd_1215737 : Nat := 4983230072969 + 3 ^ 40 * 1215737 * 2
def baseEnd_1215737 : Nat := 208085810151738385698811

theorem tailTrace_1215737 : CollatzResearch.WordTrace tailWord_1215737 prefixEnd_1215737 208085810151738385698811 := by
  unfold tailWord_1215737
  simp only [CollatzResearch.WordTrace]
  refine ⟨44341571196599955194333465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29561047464399970129555643 44341571196599955194333465)
  ·
    refine ⟨33256178397449966395750099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44341571196599955194333465 33256178397449966395750099)
    ·
      refine ⟨49884267596174949593625149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33256178397449966395750099 49884267596174949593625149)
      ·
        refine ⟨18706600348565606097609431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49884267596174949593625149 18706600348565606097609431)
        ·
          refine ⟨28059900522848409146414147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18706600348565606097609431 28059900522848409146414147)
          ·
            refine ⟨42089850784272613719621221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28059900522848409146414147 42089850784272613719621221)
            ·
              refine ⟨7891847022051115072428979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42089850784272613719621221 7891847022051115072428979)
              ·
                refine ⟨11837770533076672608643469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7891847022051115072428979 11837770533076672608643469)
                ·
                  refine ⟨4439163949903752228241301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11837770533076672608643469 4439163949903752228241301)
                  ·
                    refine ⟨208085810151738385698811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4439163949903752228241301 208085810151738385698811)
                    ·
                      rfl

theorem cell23_1215737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_1215737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215737 prefixEnd_1215737 := by exact prefixLift 1215737
  have htrace : WordTrace (prefixWord ++ tailWord_1215737) baseStart_1215737 baseEnd_1215737 := by
    simpa [prefixWord, tailWord_1215737, baseEnd_1215737] using wordTrace_append hprefix tailTrace_1215737
  have hstable : (prefixWord ++ tailWord_1215737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215737).length < 2 ^ (prefixWord ++ tailWord_1215737).sum := by decide
  have hdescent : baseEnd_1215737 < baseStart_1215737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215748 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_1215748 : Nat := 118140960795 + 1215748 * 2 ^ 59
def prefixEnd_1215748 : Nat := 4983230072969 + 3 ^ 40 * 1215748 * 2
def baseEnd_1215748 : Nat := 624263078742414614058883

theorem tailTrace_1215748 : CollatzResearch.WordTrace tailWord_1215748 prefixEnd_1215748 624263078742414614058883 := by
  unfold tailWord_1215748
  simp only [CollatzResearch.WordTrace]
  refine ⟨22170986199780052036491949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29561314933040069381989265 22170986199780052036491949)
  ·
    refine ⟨8314119824917519513684481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22170986199780052036491949 8314119824917519513684481)
    ·
      refine ⟨6235589868688139635263361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8314119824917519513684481 6235589868688139635263361)
      ·
        refine ⟨4676692401516104726447521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6235589868688139635263361 4676692401516104726447521)
        ·
          refine ⟨3507519301137078544835641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4676692401516104726447521 3507519301137078544835641)
          ·
            refine ⟨2630639475852808908626731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3507519301137078544835641 2630639475852808908626731)
            ·
              refine ⟨3945959213779213362940097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630639475852808908626731 3945959213779213362940097)
              ·
                refine ⟨2959469410334410022205073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945959213779213362940097 2959469410334410022205073)
                ·
                  refine ⟨2219602057750807516653805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2959469410334410022205073 2219602057750807516653805)
                  ·
                    refine ⟨832350771656552818745177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2219602057750807516653805 832350771656552818745177)
                    ·
                      refine ⟨624263078742414614058883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832350771656552818745177 624263078742414614058883)
                      ·
                        rfl

theorem cell23_1215748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_1215748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215748 prefixEnd_1215748 := by exact prefixLift 1215748
  have htrace : WordTrace (prefixWord ++ tailWord_1215748) baseStart_1215748 baseEnd_1215748 := by
    simpa [prefixWord, tailWord_1215748, baseEnd_1215748] using wordTrace_append hprefix tailTrace_1215748
  have hstable : (prefixWord ++ tailWord_1215748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215748).length < 2 ^ (prefixWord ++ tailWord_1215748).sum := by decide
  have hdescent : baseEnd_1215748 < baseStart_1215748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215755 : List Nat := [1, 1, 1, 1, 5, 4, 3, 2, 1, 1, 3]
def baseStart_1215755 : Nat := 118140960795 + 1215755 * 2 ^ 59
def prefixEnd_1215755 : Nat := 4983230072969 + 3 ^ 40 * 1215755 * 2
def baseEnd_1215755 : Nat := 624266673106996086671351

theorem tailTrace_1215755 : CollatzResearch.WordTrace tailWord_1215755 prefixEnd_1215755 624266673106996086671351 := by
  unfold tailWord_1215755
  simp only [CollatzResearch.WordTrace]
  refine ⟨44342227710534744268488719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29561485140356496178992479 44342227710534744268488719)
  ·
    refine ⟨66513341565802116402733079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44342227710534744268488719 66513341565802116402733079)
    ·
      refine ⟨99770012348703174604099619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66513341565802116402733079 99770012348703174604099619)
      ·
        refine ⟨149655018523054761906149429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99770012348703174604099619 149655018523054761906149429)
        ·
          refine ⟨14030157986536383928701509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149655018523054761906149429 14030157986536383928701509)
          ·
            refine ⟨2630654622475571986631533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14030157986536383928701509 2630654622475571986631533)
            ·
              refine ⟨986495483428339494986825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2630654622475571986631533 986495483428339494986825)
              ·
                refine ⟨739871612571254621240119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986495483428339494986825 739871612571254621240119)
                ·
                  refine ⟨1109807418856881931860179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 739871612571254621240119 1109807418856881931860179)
                  ·
                    refine ⟨1664711128285322897790269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1109807418856881931860179 1664711128285322897790269)
                    ·
                      refine ⟨624266673106996086671351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1664711128285322897790269 624266673106996086671351)
                      ·
                        rfl

theorem cell23_1215755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 1, 1, 3].length) (baseStart_1215755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215755 prefixEnd_1215755 := by exact prefixLift 1215755
  have htrace : WordTrace (prefixWord ++ tailWord_1215755) baseStart_1215755 baseEnd_1215755 := by
    simpa [prefixWord, tailWord_1215755, baseEnd_1215755] using wordTrace_append hprefix tailTrace_1215755
  have hstable : (prefixWord ++ tailWord_1215755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215755).length < 2 ^ (prefixWord ++ tailWord_1215755).sum := by decide
  have hdescent : baseEnd_1215755 < baseStart_1215755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215762 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 6]
def baseStart_1215762 : Nat := 118140960795 + 1215762 * 2 ^ 59
def prefixEnd_1215762 : Nat := 4983230072969 + 3 ^ 40 * 1215762 * 2
def baseEnd_1215762 : Nat := 69363363052397506587091

theorem tailTrace_1215762 : CollatzResearch.WordTrace tailWord_1215762 prefixEnd_1215762 69363363052397506587091 := by
  unfold tailWord_1215762
  simp only [CollatzResearch.WordTrace]
  refine ⟨11085620755377346115998385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29561655347672922975995693 11085620755377346115998385)
  ·
    refine ⟨8314215566533009586998789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11085620755377346115998385 8314215566533009586998789)
    ·
      refine ⟨1558915418724939297562273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8314215566533009586998789 1558915418724939297562273)
      ·
        refine ⟨1169186564043704473171705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1558915418724939297562273 1169186564043704473171705)
        ·
          refine ⟨876889923032778354878779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1169186564043704473171705 876889923032778354878779)
          ·
            refine ⟨1315334884549167532318169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876889923032778354878779 1315334884549167532318169)
            ·
              refine ⟨986501163411875649238627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315334884549167532318169 986501163411875649238627)
              ·
                refine ⟨1479751745117813473857941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986501163411875649238627 1479751745117813473857941)
                ·
                  refine ⟨69363363052397506587091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1479751745117813473857941 69363363052397506587091)
                  ·
                    rfl

theorem cell23_1215762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_1215762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215762 prefixEnd_1215762 := by exact prefixLift 1215762
  have htrace : WordTrace (prefixWord ++ tailWord_1215762) baseStart_1215762 baseEnd_1215762 := by
    simpa [prefixWord, tailWord_1215762, baseEnd_1215762] using wordTrace_append hprefix tailTrace_1215762
  have hstable : (prefixWord ++ tailWord_1215762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215762).length < 2 ^ (prefixWord ++ tailWord_1215762).sum := by decide
  have hdescent : baseEnd_1215762 < baseStart_1215762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215781 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_1215781 : Nat := 118140960795 + 1215781 * 2 ^ 59
def prefixEnd_1215781 : Nat := 4983230072969 + 3 ^ 40 * 1215781 * 2
def baseEnd_1215781 : Nat := 624280023604012984946231

theorem tailTrace_1215781 : CollatzResearch.WordTrace tailWord_1215781 prefixEnd_1215781 624280023604012984946231 := by
  unfold tailWord_1215781
  simp only [CollatzResearch.WordTrace]
  refine ⟨44343176008440550708935197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29562117338960367139290131 44343176008440550708935197)
  ·
    refine ⟨16628691003165206515850699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44343176008440550708935197 16628691003165206515850699)
    ·
      refine ⟨24943036504747809773776049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16628691003165206515850699 24943036504747809773776049)
      ·
        refine ⟨18707277378560857330332037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24943036504747809773776049 18707277378560857330332037)
        ·
          refine ⟨3507614508480160749437257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18707277378560857330332037 3507614508480160749437257)
          ·
            refine ⟨2630710881360120562077943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3507614508480160749437257 2630710881360120562077943)
            ·
              refine ⟨3946066322040180843116915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2630710881360120562077943 3946066322040180843116915)
              ·
                refine ⟨5919099483060271264675373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946066322040180843116915 5919099483060271264675373)
                ·
                  refine ⟨2219662306147601724253265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5919099483060271264675373 2219662306147601724253265)
                  ·
                    refine ⟨1664746729610701293189949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2219662306147601724253265 1664746729610701293189949)
                    ·
                      refine ⟨624280023604012984946231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1664746729610701293189949 624280023604012984946231)
                      ·
                        rfl

theorem cell23_1215781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_1215781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215781 prefixEnd_1215781 := by exact prefixLift 1215781
  have htrace : WordTrace (prefixWord ++ tailWord_1215781) baseStart_1215781 baseEnd_1215781 := by
    simpa [prefixWord, tailWord_1215781, baseEnd_1215781] using wordTrace_append hprefix tailTrace_1215781
  have hstable : (prefixWord ++ tailWord_1215781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215781).length < 2 ^ (prefixWord ++ tailWord_1215781).sum := by decide
  have hdescent : baseEnd_1215781 < baseStart_1215781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215784 : List Nat := [2, 1, 5, 1, 2, 1, 2, 9]
def baseStart_1215784 : Nat := 118140960795 + 1215784 * 2 ^ 59
def prefixEnd_1215784 : Nat := 4983230072969 + 3 ^ 40 * 1215784 * 2
def baseEnd_1215784 : Nat := 23121539409110239748471

theorem tailTrace_1215784 : CollatzResearch.WordTrace tailWord_1215784 prefixEnd_1215784 23121539409110239748471 := by
  unfold tailWord_1215784
  simp only [CollatzResearch.WordTrace]
  refine ⟨22171642713714841110647203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29562190284953121480862937 22171642713714841110647203)
  ·
    refine ⟨33257464070572261665970805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22171642713714841110647203 33257464070572261665970805)
    ·
      refine ⟨3117887256616149531184763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33257464070572261665970805 3117887256616149531184763)
      ·
        refine ⟨4676830884924224296777145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3117887256616149531184763 4676830884924224296777145)
        ·
          refine ⟨3507623163693168222582859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4676830884924224296777145 3507623163693168222582859)
          ·
            refine ⟨5261434745539752333874289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3507623163693168222582859 5261434745539752333874289)
            ·
              refine ⟨3946076059154814250405717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5261434745539752333874289 3946076059154814250405717)
              ·
                refine ⟨23121539409110239748471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3946076059154814250405717 23121539409110239748471)
                ·
                  rfl

theorem cell23_1215784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 9].length) (baseStart_1215784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215784 prefixEnd_1215784 := by exact prefixLift 1215784
  have htrace : WordTrace (prefixWord ++ tailWord_1215784) baseStart_1215784 baseEnd_1215784 := by
    simpa [prefixWord, tailWord_1215784, baseEnd_1215784] using wordTrace_append hprefix tailTrace_1215784
  have hstable : (prefixWord ++ tailWord_1215784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215784).length < 2 ^ (prefixWord ++ tailWord_1215784).sum := by decide
  have hdescent : baseEnd_1215784 < baseStart_1215784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215805 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_1215805 : Nat := 118140960795 + 1215805 * 2 ^ 59
def prefixEnd_1215805 : Nat := 4983230072969 + 3 ^ 40 * 1215805 * 2
def baseEnd_1215805 : Nat := 208097449046573630348707

theorem tailTrace_1215805 : CollatzResearch.WordTrace tailWord_1215805 prefixEnd_1215805 208097449046573630348707 := by
  unfold tailWord_1215805
  simp only [CollatzResearch.WordTrace]
  refine ⟨44344051360353602807808869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29562700906902401871872579 44344051360353602807808869)
  ·
    refine ⟨8314509630066300526464163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44344051360353602807808869 8314509630066300526464163)
    ·
      refine ⟨12471764445099450789696245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8314509630066300526464163 12471764445099450789696245)
      ·
        refine ⟨1169227916728073511534023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12471764445099450789696245 1169227916728073511534023)
        ·
          refine ⟨1753841875092110267301035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1169227916728073511534023 1753841875092110267301035)
          ·
            refine ⟨2630762812638165400951553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1753841875092110267301035 2630762812638165400951553)
            ·
              refine ⟨1973072109478624050713665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2630762812638165400951553 1973072109478624050713665)
              ·
                refine ⟨1479804082108968038035249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973072109478624050713665 1479804082108968038035249)
                ·
                  refine ⟨1109853061581726028526437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1479804082108968038035249 1109853061581726028526437)
                  ·
                    refine ⟨208097449046573630348707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1109853061581726028526437 208097449046573630348707)
                    ·
                      rfl

theorem cell23_1215805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_1215805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215805 prefixEnd_1215805 := by exact prefixLift 1215805
  have htrace : WordTrace (prefixWord ++ tailWord_1215805) baseStart_1215805 baseEnd_1215805 := by
    simpa [prefixWord, tailWord_1215805, baseEnd_1215805] using wordTrace_append hprefix tailTrace_1215805
  have hstable : (prefixWord ++ tailWord_1215805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215805).length < 2 ^ (prefixWord ++ tailWord_1215805).sum := by decide
  have hdescent : baseEnd_1215805 < baseStart_1215805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215828 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_1215828 : Nat := 118140960795 + 1215828 * 2 ^ 59
def prefixEnd_1215828 : Nat := 4983230072969 + 3 ^ 40 * 1215828 * 2
def baseEnd_1215828 : Nat := 624304157194774301058515

theorem tailTrace_1215828 : CollatzResearch.WordTrace tailWord_1215828 prefixEnd_1215828 624304157194774301058515 := by
  unfold tailWord_1215828
  simp only [CollatzResearch.WordTrace]
  refine ⟨22172445119635138867948069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29563260159513518490597425 22172445119635138867948069)
  ·
    refine ⟨4157333459931588537740263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22172445119635138867948069 4157333459931588537740263)
    ·
      refine ⟨6236000189897382806610395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4157333459931588537740263 6236000189897382806610395)
      ·
        refine ⟨9354000284846074209915593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6236000189897382806610395 9354000284846074209915593)
        ·
          refine ⟨7015500213634555657436695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9354000284846074209915593 7015500213634555657436695)
          ·
            refine ⟨10523250320451833486155043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7015500213634555657436695 10523250320451833486155043)
            ·
              refine ⟨15784875480677750229232565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10523250320451833486155043 15784875480677750229232565)
              ·
                refine ⟨1479832076313539083990553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15784875480677750229232565 1479832076313539083990553)
                ·
                  refine ⟨1109874057235154312992915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1479832076313539083990553 1109874057235154312992915)
                  ·
                    refine ⟨1664811085852731469489373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1109874057235154312992915 1664811085852731469489373)
                    ·
                      refine ⟨624304157194774301058515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1664811085852731469489373 624304157194774301058515)
                      ·
                        rfl

theorem cell23_1215828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_1215828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215828 prefixEnd_1215828 := by exact prefixLift 1215828
  have htrace : WordTrace (prefixWord ++ tailWord_1215828) baseStart_1215828 baseEnd_1215828 := by
    simpa [prefixWord, tailWord_1215828, baseEnd_1215828] using wordTrace_append hprefix tailTrace_1215828
  have hstable : (prefixWord ++ tailWord_1215828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215828).length < 2 ^ (prefixWord ++ tailWord_1215828).sum := by decide
  have hdescent : baseEnd_1215828 < baseStart_1215828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215868 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_1215868 : Nat := 118140960795 + 1215868 * 2 ^ 59
def prefixEnd_1215868 : Nat := 4983230072969 + 3 ^ 40 * 1215868 * 2
def baseEnd_1215868 : Nat := 624324696420954144558331

theorem tailTrace_1215868 : CollatzResearch.WordTrace tailWord_1215868 prefixEnd_1215868 624324696420954144558331 := by
  unfold tailWord_1215868
  simp only [CollatzResearch.WordTrace]
  refine ⟨22173174579562682283676129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29564232772750243044901505 22173174579562682283676129)
  ·
    refine ⟨16629880934672011712757097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22173174579562682283676129 16629880934672011712757097)
    ·
      refine ⟨12472410701004008784567823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16629880934672011712757097 12472410701004008784567823)
      ·
        refine ⟨18708616051506013176851735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12472410701004008784567823 18708616051506013176851735)
        ·
          refine ⟨28062924077259019765277603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18708616051506013176851735 28062924077259019765277603)
          ·
            refine ⟨42094386115888529647916405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28062924077259019765277603 42094386115888529647916405)
            ·
              refine ⟨3946348698364549654492163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42094386115888529647916405 3946348698364549654492163)
              ·
                refine ⟨5919523047546824481738245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946348698364549654492163 5919523047546824481738245)
                ·
                  refine ⟨1109910571415029590325921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5919523047546824481738245 1109910571415029590325921)
                  ·
                    refine ⟨832432928561272192744441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1109910571415029590325921 832432928561272192744441)
                    ·
                      refine ⟨624324696420954144558331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832432928561272192744441 624324696420954144558331)
                      ·
                        rfl

theorem cell23_1215868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_1215868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215868 prefixEnd_1215868 := by exact prefixLift 1215868
  have htrace : WordTrace (prefixWord ++ tailWord_1215868) baseStart_1215868 baseEnd_1215868 := by
    simpa [prefixWord, tailWord_1215868, baseEnd_1215868] using wordTrace_append hprefix tailTrace_1215868
  have hstable : (prefixWord ++ tailWord_1215868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215868).length < 2 ^ (prefixWord ++ tailWord_1215868).sum := by decide
  have hdescent : baseEnd_1215868 < baseStart_1215868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215904 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 1, 7]
def baseStart_1215904 : Nat := 118140960795 + 1215904 * 2 ^ 59
def prefixEnd_1215904 : Nat := 4983230072969 + 3 ^ 40 * 1215904 * 2
def baseEnd_1215904 : Nat := 208114393908172001236055

theorem tailTrace_1215904 : CollatzResearch.WordTrace tailWord_1215904 prefixEnd_1215904 208114393908172001236055 := by
  unfold tailWord_1215904
  simp only [CollatzResearch.WordTrace]
  refine ⟨22173831093497471357831383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29565108124663295143775177 22173831093497471357831383)
  ·
    refine ⟨33260746640246207036747075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22173831093497471357831383 33260746640246207036747075)
    ·
      refine ⟨49891119960369310555120613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33260746640246207036747075 49891119960369310555120613)
      ·
        refine ⟨9354584992569245729085115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49891119960369310555120613 9354584992569245729085115)
        ·
          refine ⟨14031877488853868593627673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9354584992569245729085115 14031877488853868593627673)
          ·
            refine ⟨10523908116640401445220755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14031877488853868593627673 10523908116640401445220755)
            ·
              refine ⟨15785862174960602167831133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10523908116640401445220755 15785862174960602167831133)
              ·
                refine ⟨5919698315610225812936675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15785862174960602167831133 5919698315610225812936675)
                ·
                  refine ⟨8879547473415338719405013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5919698315610225812936675 8879547473415338719405013)
                  ·
                    refine ⟨208114393908172001236055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8879547473415338719405013 208114393908172001236055)
                    ·
                      rfl

theorem cell23_1215904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_1215904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215904 prefixEnd_1215904 := by exact prefixLift 1215904
  have htrace : WordTrace (prefixWord ++ tailWord_1215904) baseStart_1215904 baseEnd_1215904 := by
    simpa [prefixWord, tailWord_1215904, baseEnd_1215904] using wordTrace_append hprefix tailTrace_1215904
  have hstable : (prefixWord ++ tailWord_1215904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215904).length < 2 ^ (prefixWord ++ tailWord_1215904).sum := by decide
  have hdescent : baseEnd_1215904 < baseStart_1215904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215921 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 2, 5]
def baseStart_1215921 : Nat := 118140960795 + 1215921 * 2 ^ 59
def prefixEnd_1215921 : Nat := 4983230072969 + 3 ^ 40 * 1215921 * 2
def baseEnd_1215921 : Nat := 208117303631880812398529

theorem tailTrace_1215921 : CollatzResearch.WordTrace tailWord_1215921 prefixEnd_1215921 208117303631880812398529 := by
  unfold tailWord_1215921
  simp only [CollatzResearch.WordTrace]
  refine ⟨44348282227933354619031617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29565521485288903079354411 44348282227933354619031617)
  ·
    refine ⟨33261211670950015964273713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44348282227933354619031617 33261211670950015964273713)
    ·
      refine ⟨24945908753212511973205285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33261211670950015964273713 24945908753212511973205285)
      ·
        refine ⟨4677357891227345994975991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24945908753212511973205285 4677357891227345994975991)
        ·
          refine ⟨7016036836841018992463987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4677357891227345994975991 7016036836841018992463987)
          ·
            refine ⟨10524055255261528488695981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016036836841018992463987 10524055255261528488695981)
            ·
              refine ⟨3946520720723073183260993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10524055255261528488695981 3946520720723073183260993)
              ·
                refine ⟨2959890540542304887445745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3946520720723073183260993 2959890540542304887445745)
                ·
                  refine ⟨2219917905406728665584309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2959890540542304887445745 2219917905406728665584309)
                  ·
                    refine ⟨208117303631880812398529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2219917905406728665584309 208117303631880812398529)
                    ·
                      rfl

theorem cell23_1215921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_1215921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215921 prefixEnd_1215921 := by exact prefixLift 1215921
  have htrace : WordTrace (prefixWord ++ tailWord_1215921) baseStart_1215921 baseEnd_1215921 := by
    simpa [prefixWord, tailWord_1215921, baseEnd_1215921] using wordTrace_append hprefix tailTrace_1215921
  have hstable : (prefixWord ++ tailWord_1215921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215921).length < 2 ^ (prefixWord ++ tailWord_1215921).sum := by decide
  have hdescent : baseEnd_1215921 < baseStart_1215921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215925 : List Nat := [1, 3, 3, 2, 2, 2, 3, 2, 5]
def baseStart_1215925 : Nat := 118140960795 + 1215925 * 2 ^ 59
def prefixEnd_1215925 : Nat := 4983230072969 + 3 ^ 40 * 1215925 * 2
def baseEnd_1215925 : Nat := 69372662757584491282841

theorem tailTrace_1215925 : CollatzResearch.WordTrace tailWord_1215925 prefixEnd_1215925 69372662757584491282841 := by
  unfold tailWord_1215925
  simp only [CollatzResearch.WordTrace]
  refine ⟨44348428119918863302177229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29565618746612575534784819 44348428119918863302177229)
  ·
    refine ⟨16630660544969573738316461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44348428119918863302177229 16630660544969573738316461)
    ·
      refine ⟨6236497704363590151868673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16630660544969573738316461 6236497704363590151868673)
      ·
        refine ⟨4677373278272692613901505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6236497704363590151868673 4677373278272692613901505)
        ·
          refine ⟨3508029958704519460426129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4677373278272692613901505 3508029958704519460426129)
          ·
            refine ⟨2631022469028389595319597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3508029958704519460426129 2631022469028389595319597)
            ·
              refine ⟨986633425885646098244849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2631022469028389595319597 986633425885646098244849)
              ·
                refine ⟨739975069414234573683637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986633425885646098244849 739975069414234573683637)
                ·
                  refine ⟨69372662757584491282841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 739975069414234573683637 69372662757584491282841)
                  ·
                    rfl

theorem cell23_1215925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_1215925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215925 prefixEnd_1215925 := by exact prefixLift 1215925
  have htrace : WordTrace (prefixWord ++ tailWord_1215925) baseStart_1215925 baseEnd_1215925 := by
    simpa [prefixWord, tailWord_1215925, baseEnd_1215925] using wordTrace_append hprefix tailTrace_1215925
  have hstable : (prefixWord ++ tailWord_1215925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215925).length < 2 ^ (prefixWord ++ tailWord_1215925).sum := by decide
  have hdescent : baseEnd_1215925 < baseStart_1215925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215951 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 3, 4]
def baseStart_1215951 : Nat := 118140960795 + 1215951 * 2 ^ 59
def prefixEnd_1215951 : Nat := 4983230072969 + 3 ^ 40 * 1215951 * 2
def baseEnd_1215951 : Nat := 208122438438425773273483

theorem tailTrace_1215951 : CollatzResearch.WordTrace tailWord_1215951 prefixEnd_1215951 208122438438425773273483 := by
  unfold tailWord_1215951
  simp only [CollatzResearch.WordTrace]
  refine ⟨44349376417824669742623707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29566250945216446495082471 44349376417824669742623707)
  ·
    refine ⟨66524064626737004613935561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44349376417824669742623707 66524064626737004613935561)
    ·
      refine ⟨49893048470052753460451671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66524064626737004613935561 49893048470052753460451671)
      ·
        refine ⟨74839572705079130190677507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49893048470052753460451671 74839572705079130190677507)
        ·
          refine ⟨112259359057618695286016261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74839572705079130190677507 112259359057618695286016261)
          ·
            refine ⟨21048629823303505366128049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112259359057618695286016261 21048629823303505366128049)
            ·
              refine ⟨15786472367477629024596037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21048629823303505366128049 15786472367477629024596037)
              ·
                refine ⟨2959963568902055442111757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15786472367477629024596037 2959963568902055442111757)
                ·
                  refine ⟨1109986338338270790791909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2959963568902055442111757 1109986338338270790791909)
                  ·
                    refine ⟨208122438438425773273483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1109986338338270790791909 208122438438425773273483)
                    ·
                      rfl

theorem cell23_1215951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 4].length) (baseStart_1215951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215951 prefixEnd_1215951 := by exact prefixLift 1215951
  have htrace : WordTrace (prefixWord ++ tailWord_1215951) baseStart_1215951 baseEnd_1215951 := by
    simpa [prefixWord, tailWord_1215951, baseEnd_1215951] using wordTrace_append hprefix tailTrace_1215951
  have hstable : (prefixWord ++ tailWord_1215951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215951).length < 2 ^ (prefixWord ++ tailWord_1215951).sum := by decide
  have hdescent : baseEnd_1215951 < baseStart_1215951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215985 : List Nat := [1, 2, 2, 2, 3, 3, 1, 4, 1, 4]
def baseStart_1215985 : Nat := 118140960795 + 1215985 * 2 ^ 59
def prefixEnd_1215985 : Nat := 4983230072969 + 3 ^ 40 * 1215985 * 2
def baseEnd_1215985 : Nat := 208128257885843395598431

theorem tailTrace_1215985 : CollatzResearch.WordTrace tailWord_1215985 prefixEnd_1215985 208128257885843395598431 := by
  unfold tailWord_1215985
  simp only [CollatzResearch.WordTrace]
  refine ⟨44350616499701493549361409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29567077666467662366240939 44350616499701493549361409)
  ·
    refine ⟨33262962374776120162021057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44350616499701493549361409 33262962374776120162021057)
    ·
      refine ⟨24947221781082090121515793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33262962374776120162021057 24947221781082090121515793)
      ·
        refine ⟨18710416335811567591136845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24947221781082090121515793 18710416335811567591136845)
        ·
          refine ⟨7016406125929337846676317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18710416335811567591136845 7016406125929337846676317)
          ·
            refine ⟨2631152297223501692503619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7016406125929337846676317 2631152297223501692503619)
            ·
              refine ⟨3946728445835252538755429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631152297223501692503619 3946728445835252538755429)
              ·
                refine ⟨740011583594109851016643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3946728445835252538755429 740011583594109851016643)
                ·
                  refine ⟨1110017375391164776524965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740011583594109851016643 1110017375391164776524965)
                  ·
                    refine ⟨208128257885843395598431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1110017375391164776524965 208128257885843395598431)
                    ·
                      rfl

theorem cell23_1215985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_1215985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1215985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1215985 prefixEnd_1215985 := by exact prefixLift 1215985
  have htrace : WordTrace (prefixWord ++ tailWord_1215985) baseStart_1215985 baseEnd_1215985 := by
    simpa [prefixWord, tailWord_1215985, baseEnd_1215985] using wordTrace_append hprefix tailTrace_1215985
  have hstable : (prefixWord ++ tailWord_1215985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215985).length < 2 ^ (prefixWord ++ tailWord_1215985).sum := by decide
  have hdescent : baseEnd_1215985 < baseStart_1215985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216006 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1216006 : Nat := 118140960795 + 1216006 * 2 ^ 59
def prefixEnd_1216006 : Nat := 4983230072969 + 3 ^ 40 * 1216006 * 2
def baseEnd_1216006 : Nat := 208131852250424868210899

theorem tailTrace_1216006 : CollatzResearch.WordTrace tailWord_1216006 prefixEnd_1216006 208131852250424868210899 := by
  unfold tailWord_1216006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385980701019544191746121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29567588288416942757250581 1385980701019544191746121)
  ·
    refine ⟨1039485525764658143809591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1385980701019544191746121 1039485525764658143809591)
    ·
      refine ⟨1559228288646987215714387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1039485525764658143809591 1559228288646987215714387)
      ·
        refine ⟨2338842432970480823571581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559228288646987215714387 2338842432970480823571581)
        ·
          refine ⟨877065912363930308839343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2338842432970480823571581 877065912363930308839343)
          ·
            refine ⟨1315598868545895463259015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877065912363930308839343 1315598868545895463259015)
            ·
              refine ⟨1973398302818843194888523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315598868545895463259015 1973398302818843194888523)
              ·
                refine ⟨2960097454228264792332785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973398302818843194888523 2960097454228264792332785)
                ·
                  refine ⟨2220073090671198594249589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2960097454228264792332785 2220073090671198594249589)
                  ·
                    refine ⟨208131852250424868210899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2220073090671198594249589 208131852250424868210899)
                    ·
                      rfl

theorem cell23_1216006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1216006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216006 prefixEnd_1216006 := by exact prefixLift 1216006
  have htrace : WordTrace (prefixWord ++ tailWord_1216006) baseStart_1216006 baseEnd_1216006 := by
    simpa [prefixWord, tailWord_1216006, baseEnd_1216006] using wordTrace_append hprefix tailTrace_1216006
  have hstable : (prefixWord ++ tailWord_1216006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216006).length < 2 ^ (prefixWord ++ tailWord_1216006).sum := by decide
  have hdescent : baseEnd_1216006 < baseStart_1216006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216008 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_1216008 : Nat := 118140960795 + 1216008 * 2 ^ 59
def prefixEnd_1216008 : Nat := 4983230072969 + 3 ^ 40 * 1216008 * 2
def baseEnd_1216008 : Nat := 624396583712583596807687

theorem tailTrace_1216008 : CollatzResearch.WordTrace tailWord_1216008 prefixEnd_1216008 624396583712583596807687 := by
  unfold tailWord_1216008
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175727689309084238724339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29567636919078778984965785 22175727689309084238724339)
  ·
    refine ⟨33263591533963626358086509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22175727689309084238724339 33263591533963626358086509)
    ·
      refine ⟨12473846825236359884282441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33263591533963626358086509 12473846825236359884282441)
      ·
        refine ⟨9355385118927269913211831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12473846825236359884282441 9355385118927269913211831)
        ·
          refine ⟨14033077678390904869817747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9355385118927269913211831 14033077678390904869817747)
          ·
            refine ⟨21049616517586357304726621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14033077678390904869817747 21049616517586357304726621)
            ·
              refine ⟨7893606194094883989272483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21049616517586357304726621 7893606194094883989272483)
              ·
                refine ⟨11840409291142325983908725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7893606194094883989272483 11840409291142325983908725)
                ·
                  refine ⟨1110038371044593060991443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11840409291142325983908725 1110038371044593060991443)
                  ·
                    refine ⟨1665057556566889591487165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1110038371044593060991443 1665057556566889591487165)
                    ·
                      refine ⟨624396583712583596807687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1665057556566889591487165 624396583712583596807687)
                      ·
                        rfl

theorem cell23_1216008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_1216008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216008 prefixEnd_1216008 := by exact prefixLift 1216008
  have htrace : WordTrace (prefixWord ++ tailWord_1216008) baseStart_1216008 baseEnd_1216008 := by
    simpa [prefixWord, tailWord_1216008, baseEnd_1216008] using wordTrace_append hprefix tailTrace_1216008
  have hstable : (prefixWord ++ tailWord_1216008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216008).length < 2 ^ (prefixWord ++ tailWord_1216008).sum := by decide
  have hdescent : baseEnd_1216008 < baseStart_1216008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216012 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 2, 2, 3]
def baseStart_1216012 : Nat := 118140960795 + 1216012 * 2 ^ 59
def prefixEnd_1216012 : Nat := 4983230072969 + 3 ^ 40 * 1216012 * 2
def baseEnd_1216012 : Nat := 624398637635201581157669

theorem tailTrace_1216012 : CollatzResearch.WordTrace tailWord_1216012 prefixEnd_1216012 624398637635201581157669 := by
  unfold tailWord_1216012
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175800635301838580297145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29567734180402451440396193 22175800635301838580297145)
  ·
    refine ⟨16631850476476378935222859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22175800635301838580297145 16631850476476378935222859)
    ·
      refine ⟨24947775714714568402834289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16631850476476378935222859 24947775714714568402834289)
      ·
        refine ⟨18710831786035926302125717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24947775714714568402834289 18710831786035926302125717)
        ·
          refine ⟨877070239970434045412143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18710831786035926302125717 877070239970434045412143)
          ·
            refine ⟨1315605359955651068118215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877070239970434045412143 1315605359955651068118215)
            ·
              refine ⟨1973408039933476602177323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315605359955651068118215 1973408039933476602177323)
              ·
                refine ⟨2960112059900214903265985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973408039933476602177323 2960112059900214903265985)
                ·
                  refine ⟨2220084044925161177449489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2960112059900214903265985 2220084044925161177449489)
                  ·
                    refine ⟨1665063033693870883087117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2220084044925161177449489 1665063033693870883087117)
                    ·
                      refine ⟨624398637635201581157669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1665063033693870883087117 624398637635201581157669)
                      ·
                        rfl

theorem cell23_1216012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_1216012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216012 prefixEnd_1216012 := by exact prefixLift 1216012
  have htrace : WordTrace (prefixWord ++ tailWord_1216012) baseStart_1216012 baseEnd_1216012 := by
    simpa [prefixWord, tailWord_1216012, baseEnd_1216012] using wordTrace_append hprefix tailTrace_1216012
  have hstable : (prefixWord ++ tailWord_1216012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216012).length < 2 ^ (prefixWord ++ tailWord_1216012).sum := by decide
  have hdescent : baseEnd_1216012 < baseStart_1216012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216028 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1216028 : Nat := 118140960795 + 1216028 * 2 ^ 59
def prefixEnd_1216028 : Nat := 4983230072969 + 3 ^ 40 * 1216028 * 2
def baseEnd_1216028 : Nat := 208135617775224506185865

theorem tailTrace_1216028 : CollatzResearch.WordTrace tailWord_1216028 prefixEnd_1216028 208135617775224506185865 := by
  unfold tailWord_1216028
  simp only [CollatzResearch.WordTrace]
  refine ⟨22176092419272855946588369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29568123225697141262117825 22176092419272855946588369)
  ·
    refine ⟨16632069314454641959941277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22176092419272855946588369 16632069314454641959941277)
    ·
      refine ⟨6237025992920490734977979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16632069314454641959941277 6237025992920490734977979)
      ·
        refine ⟨9355538989380736102466969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6237025992920490734977979 9355538989380736102466969)
        ·
          refine ⟨7016654242035552076850227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9355538989380736102466969 7016654242035552076850227)
          ·
            refine ⟨10524981363053328115275341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016654242035552076850227 10524981363053328115275341)
            ·
              refine ⟨3946868011144998043228253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10524981363053328115275341 3946868011144998043228253)
              ·
                refine ⟨1480075504179374266210595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3946868011144998043228253 1480075504179374266210595)
                ·
                  refine ⟨2220113256269061399315893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480075504179374266210595 2220113256269061399315893)
                  ·
                    refine ⟨208135617775224506185865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2220113256269061399315893 208135617775224506185865)
                    ·
                      rfl

theorem cell23_1216028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1216028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216028 prefixEnd_1216028 := by exact prefixLift 1216028
  have htrace : WordTrace (prefixWord ++ tailWord_1216028) baseStart_1216028 baseEnd_1216028 := by
    simpa [prefixWord, tailWord_1216028, baseEnd_1216028] using wordTrace_append hprefix tailTrace_1216028
  have hstable : (prefixWord ++ tailWord_1216028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216028).length < 2 ^ (prefixWord ++ tailWord_1216028).sum := by decide
  have hdescent : baseEnd_1216028 < baseStart_1216028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216042 : List Nat := [3, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_1216042 : Nat := 118140960795 + 1216042 * 2 ^ 59
def prefixEnd_1216042 : Nat := 4983230072969 + 3 ^ 40 * 1216042 * 2
def baseEnd_1216042 : Nat := 624414042054836463782531

theorem tailTrace_1216042 : CollatzResearch.WordTrace tailWord_1216042 prefixEnd_1216042 624414042054836463782531 := by
  unfold tailWord_1216042
  simp only [CollatzResearch.WordTrace]
  refine ⟨11088173865123748071046595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29568463640329994856124253 11088173865123748071046595)
  ·
    refine ⟨16632260797685622106569893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11088173865123748071046595 16632260797685622106569893)
    ·
      refine ⟨3118548899566054144981855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16632260797685622106569893 3118548899566054144981855)
      ·
        refine ⟨4677823349349081217472783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3118548899566054144981855 4677823349349081217472783)
        ·
          refine ⟨7016735024023621826209175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4677823349349081217472783 7016735024023621826209175)
          ·
            refine ⟨10525102536035432739313763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016735024023621826209175 10525102536035432739313763)
            ·
              refine ⟨15787653804053149108970645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10525102536035432739313763 15787653804053149108970645)
              ·
                refine ⟨740046272064991364482999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15787653804053149108970645 740046272064991364482999)
                ·
                  refine ⟨1110069408097487046724499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740046272064991364482999 1110069408097487046724499)
                  ·
                    refine ⟨1665104112146230570086749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1110069408097487046724499 1665104112146230570086749)
                    ·
                      refine ⟨624414042054836463782531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1665104112146230570086749 624414042054836463782531)
                      ·
                        rfl

theorem cell23_1216042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_1216042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216042 prefixEnd_1216042 := by exact prefixLift 1216042
  have htrace : WordTrace (prefixWord ++ tailWord_1216042) baseStart_1216042 baseEnd_1216042 := by
    simpa [prefixWord, tailWord_1216042, baseEnd_1216042] using wordTrace_append hprefix tailTrace_1216042
  have hstable : (prefixWord ++ tailWord_1216042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216042).length < 2 ^ (prefixWord ++ tailWord_1216042).sum := by decide
  have hdescent : baseEnd_1216042 < baseStart_1216042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216051 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 5]
def baseStart_1216051 : Nat := 118140960795 + 1216051 * 2 ^ 59
def prefixEnd_1216051 : Nat := 4983230072969 + 3 ^ 40 * 1216051 * 2
def baseEnd_1216051 : Nat := 624418663380726928569989

theorem tailTrace_1216051 : CollatzResearch.WordTrace tailWord_1216051 prefixEnd_1216051 624418663380726928569989 := by
  unfold tailWord_1216051
  simp only [CollatzResearch.WordTrace]
  refine ⟨44353023717462386821264007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29568682478308257880842671 44353023717462386821264007)
  ·
    refine ⟨66529535576193580231896011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44353023717462386821264007 66529535576193580231896011)
    ·
      refine ⟨99794303364290370347844017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66529535576193580231896011 99794303364290370347844017)
      ·
        refine ⟨74845727523217777760883013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99794303364290370347844017 74845727523217777760883013)
        ·
          refine ⟨14033573910603333330165565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74845727523217777760883013 14033573910603333330165565)
          ·
            refine ⟨5262590216476249998812087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14033573910603333330165565 5262590216476249998812087)
            ·
              refine ⟨7893885324714374998218131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262590216476249998812087 7893885324714374998218131)
              ·
                refine ⟨11840827987071562497327197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7893885324714374998218131 11840827987071562497327197)
                ·
                  refine ⟨4440310495151835936497699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11840827987071562497327197 4440310495151835936497699)
                  ·
                    refine ⟨6660465742727753904746549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4440310495151835936497699 6660465742727753904746549)
                    ·
                      refine ⟨624418663380726928569989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6660465742727753904746549 624418663380726928569989)
                      ·
                        rfl

theorem cell23_1216051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_1216051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216051 prefixEnd_1216051 := by exact prefixLift 1216051
  have htrace : WordTrace (prefixWord ++ tailWord_1216051) baseStart_1216051 baseEnd_1216051 := by
    simpa [prefixWord, tailWord_1216051, baseEnd_1216051] using wordTrace_append hprefix tailTrace_1216051
  have hstable : (prefixWord ++ tailWord_1216051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216051).length < 2 ^ (prefixWord ++ tailWord_1216051).sum := by decide
  have hdescent : baseEnd_1216051 < baseStart_1216051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216065 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1216065 : Nat := 118140960795 + 1216065 * 2 ^ 59
def prefixEnd_1216065 : Nat := 4983230072969 + 3 ^ 40 * 1216065 * 2
def baseEnd_1216065 : Nat := 624425852109889873794925

theorem tailTrace_1216065 : CollatzResearch.WordTrace tailWord_1216065 prefixEnd_1216065 624425852109889873794925 := by
  unfold tailWord_1216065
  simp only [CollatzResearch.WordTrace]
  refine ⟨44353534339411667212273649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29569022892941111474849099 44353534339411667212273649)
  ·
    refine ⟨33265150754558750409205237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44353534339411667212273649 33265150754558750409205237)
    ·
      refine ⟨3118607883239882850862991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33265150754558750409205237 3118607883239882850862991)
      ·
        refine ⟨4677911824859824276294487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3118607883239882850862991 4677911824859824276294487)
        ·
          refine ⟨7016867737289736414441731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4677911824859824276294487 7016867737289736414441731)
          ·
            refine ⟨10525301605934604621662597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016867737289736414441731 10525301605934604621662597)
            ·
              refine ⟨1973494051112738366561737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10525301605934604621662597 1973494051112738366561737)
              ·
                refine ⟨1480120538334553774921303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973494051112738366561737 1480120538334553774921303)
                ·
                  refine ⟨2220180807501830662381955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480120538334553774921303 2220180807501830662381955)
                  ·
                    refine ⟨3330271211252745993572933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2220180807501830662381955 3330271211252745993572933)
                    ·
                      refine ⟨624425852109889873794925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3330271211252745993572933 624425852109889873794925)
                      ·
                        rfl

theorem cell23_1216065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1216065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216065 prefixEnd_1216065 := by exact prefixLift 1216065
  have htrace : WordTrace (prefixWord ++ tailWord_1216065) baseStart_1216065 baseEnd_1216065 := by
    simpa [prefixWord, tailWord_1216065, baseEnd_1216065] using wordTrace_append hprefix tailTrace_1216065
  have hstable : (prefixWord ++ tailWord_1216065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216065).length < 2 ^ (prefixWord ++ tailWord_1216065).sum := by decide
  have hdescent : baseEnd_1216065 < baseStart_1216065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216086 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1216086 : Nat := 118140960795 + 1216086 * 2 ^ 59
def prefixEnd_1216086 : Nat := 4983230072969 + 3 ^ 40 * 1216086 * 2
def baseEnd_1216086 : Nat := 624436635203634291632329

theorem tailTrace_1216086 : CollatzResearch.WordTrace tailWord_1216086 prefixEnd_1216086 624436635203634291632329 := by
  unfold tailWord_1216086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2772143767020974237424257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29569533514890391865858741 2772143767020974237424257)
  ·
    refine ⟨2079107825265730678068193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2772143767020974237424257 2079107825265730678068193)
    ·
      refine ⟨1559330868949298008551145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2079107825265730678068193 1559330868949298008551145)
      ·
        refine ⟨1169498151711973506413359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1559330868949298008551145 1169498151711973506413359)
        ·
          refine ⟨1754247227567960259620039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1169498151711973506413359 1754247227567960259620039)
          ·
            refine ⟨2631370841351940389430059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754247227567960259620039 2631370841351940389430059)
            ·
              refine ⟨3947056262027910584145089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631370841351940389430059 3947056262027910584145089)
              ·
                refine ⟨2960292196520932938108817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3947056262027910584145089 2960292196520932938108817)
                ·
                  refine ⟨2220219147390699703581613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2960292196520932938108817 2220219147390699703581613)
                  ·
                    refine ⟨832582180271512388843105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2220219147390699703581613 832582180271512388843105)
                    ·
                      refine ⟨624436635203634291632329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832582180271512388843105 624436635203634291632329)
                      ·
                        rfl

theorem cell23_1216086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1216086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216086 prefixEnd_1216086 := by exact prefixLift 1216086
  have htrace : WordTrace (prefixWord ++ tailWord_1216086) baseStart_1216086 baseEnd_1216086 := by
    simpa [prefixWord, tailWord_1216086, baseEnd_1216086] using wordTrace_append hprefix tailTrace_1216086
  have hstable : (prefixWord ++ tailWord_1216086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216086).length < 2 ^ (prefixWord ++ tailWord_1216086).sum := by decide
  have hdescent : baseEnd_1216086 < baseStart_1216086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216093 : List Nat := [1, 4, 4, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_1216093 : Nat := 118140960795 + 1216093 * 2 ^ 59
def prefixEnd_1216093 : Nat := 4983230072969 + 3 ^ 40 * 1216093 * 2
def baseEnd_1216093 : Nat := 624440229568215764244797

theorem tailTrace_1216093 : CollatzResearch.WordTrace tailWord_1216093 prefixEnd_1216093 624440229568215764244797 := by
  unfold tailWord_1216093
  simp only [CollatzResearch.WordTrace]
  refine ⟨44354555583310227994292933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29569703722206818662861955 44354555583310227994292933)
  ·
    refine ⟨8316479171870667748929925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44354555583310227994292933 8316479171870667748929925)
    ·
      refine ⟨1559339844725750202924361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8316479171870667748929925 1559339844725750202924361)
      ·
        refine ⟨1169504883544312652193271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1559339844725750202924361 1169504883544312652193271)
        ·
          refine ⟨1754257325316468978289907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1169504883544312652193271 1754257325316468978289907)
          ·
            refine ⟨2631385987974703467434861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754257325316468978289907 2631385987974703467434861)
            ·
              refine ⟨986769745490513800288073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2631385987974703467434861 986769745490513800288073)
              ·
                refine ⟨740077309117885350216055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 986769745490513800288073 740077309117885350216055)
                ·
                  refine ⟨1110115963676828025324083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740077309117885350216055 1110115963676828025324083)
                  ·
                    refine ⟨1665173945515242037986125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1110115963676828025324083 1665173945515242037986125)
                    ·
                      refine ⟨624440229568215764244797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1665173945515242037986125 624440229568215764244797)
                      ·
                        rfl

theorem cell23_1216093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_1216093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216093 prefixEnd_1216093 := by exact prefixLift 1216093
  have htrace : WordTrace (prefixWord ++ tailWord_1216093) baseStart_1216093 baseEnd_1216093 := by
    simpa [prefixWord, tailWord_1216093, baseEnd_1216093] using wordTrace_append hprefix tailTrace_1216093
  have hstable : (prefixWord ++ tailWord_1216093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216093).length < 2 ^ (prefixWord ++ tailWord_1216093).sum := by decide
  have hdescent : baseEnd_1216093 < baseStart_1216093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216108 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 2, 7, 2]
def baseStart_1216108 : Nat := 118140960795 + 1216108 * 2 ^ 59
def prefixEnd_1216108 : Nat := 4983230072969 + 3 ^ 40 * 1216108 * 2
def baseEnd_1216108 : Nat := 624447931778033205557227

theorem tailTrace_1216108 : CollatzResearch.WordTrace tailWord_1216108 prefixEnd_1216108 624447931778033205557227 := by
  unfold tailWord_1216108
  simp only [CollatzResearch.WordTrace]
  refine ⟨22177551339127942778044489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29570068452170590370725985 22177551339127942778044489)
  ·
    refine ⟨16633163504345957083533367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22177551339127942778044489 16633163504345957083533367)
    ·
      refine ⟨24949745256518935625300051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16633163504345957083533367 24949745256518935625300051)
      ·
        refine ⟨37424617884778403437950077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24949745256518935625300051 37424617884778403437950077)
        ·
          refine ⟨14034231706791901289231279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37424617884778403437950077 14034231706791901289231279)
          ·
            refine ⟨21051347560187851933846919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14034231706791901289231279 21051347560187851933846919)
            ·
              refine ⟨31577021340281777900770379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21051347560187851933846919 31577021340281777900770379)
              ·
                refine ⟨47365532010422666851155569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31577021340281777900770379 47365532010422666851155569)
                ·
                  refine ⟨35524149007817000138366677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47365532010422666851155569 35524149007817000138366677)
                  ·
                    refine ⟨832597242370710940742969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35524149007817000138366677 832597242370710940742969)
                    ·
                      refine ⟨624447931778033205557227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832597242370710940742969 624447931778033205557227)
                      ·
                        rfl

theorem cell23_1216108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_1216108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216108 prefixEnd_1216108 := by exact prefixLift 1216108
  have htrace : WordTrace (prefixWord ++ tailWord_1216108) baseStart_1216108 baseEnd_1216108 := by
    simpa [prefixWord, tailWord_1216108, baseEnd_1216108] using wordTrace_append hprefix tailTrace_1216108
  have hstable : (prefixWord ++ tailWord_1216108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216108).length < 2 ^ (prefixWord ++ tailWord_1216108).sum := by decide
  have hdescent : baseEnd_1216108 < baseStart_1216108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216109 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1216109 : Nat := 118140960795 + 1216109 * 2 ^ 59
def prefixEnd_1216109 : Nat := 4983230072969 + 3 ^ 40 * 1216109 * 2
def baseEnd_1216109 : Nat := 208149481752895900548241

theorem tailTrace_1216109 : CollatzResearch.WordTrace tailWord_1216109 prefixEnd_1216109 208149481752895900548241 := by
  unfold tailWord_1216109
  simp only [CollatzResearch.WordTrace]
  refine ⟨44355139151252262726875381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29570092767501508484583587 44355139151252262726875381)
  ·
    refine ⟨4158294295429899630644567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44355139151252262726875381 4158294295429899630644567)
    ·
      refine ⟨6237441443144849445966851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4158294295429899630644567 6237441443144849445966851)
      ·
        refine ⟨9356162164717274168950277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6237441443144849445966851 9356162164717274168950277)
        ·
          refine ⟨1754280405884488906678177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9356162164717274168950277 1754280405884488906678177)
          ·
            refine ⟨1315710304413366680008633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1754280405884488906678177 1315710304413366680008633)
            ·
              refine ⟨986782728310025010006475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315710304413366680008633 986782728310025010006475)
              ·
                refine ⟨1480174092465037515009713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986782728310025010006475 1480174092465037515009713)
                ·
                  refine ⟨1110130569348778136257285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1480174092465037515009713 1110130569348778136257285)
                  ·
                    refine ⟨208149481752895900548241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1110130569348778136257285 208149481752895900548241)
                    ·
                      rfl

theorem cell23_1216109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1216109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216109 prefixEnd_1216109 := by exact prefixLift 1216109
  have htrace : WordTrace (prefixWord ++ tailWord_1216109) baseStart_1216109 baseEnd_1216109 := by
    simpa [prefixWord, tailWord_1216109, baseEnd_1216109] using wordTrace_append hprefix tailTrace_1216109
  have hstable : (prefixWord ++ tailWord_1216109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216109).length < 2 ^ (prefixWord ++ tailWord_1216109).sum := by decide
  have hdescent : baseEnd_1216109 < baseStart_1216109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216131 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 4, 6]
def baseStart_1216131 : Nat := 118140960795 + 1216131 * 2 ^ 59
def prefixEnd_1216131 : Nat := 4983230072969 + 3 ^ 40 * 1216131 * 2
def baseEnd_1216131 : Nat := 208153247277695538523207

theorem tailTrace_1216131 : CollatzResearch.WordTrace tailWord_1216131 prefixEnd_1216131 208153247277695538523207 := by
  unfold tailWord_1216131
  simp only [CollatzResearch.WordTrace]
  refine ⟨44355941557172560484176247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29570627704781706989450831 44355941557172560484176247)
  ·
    refine ⟨66533912335758840726264371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44355941557172560484176247 66533912335758840726264371)
    ·
      refine ⟨99800868503638261089396557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66533912335758840726264371 99800868503638261089396557)
      ·
        refine ⟨37425325688864347908523709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99800868503638261089396557 37425325688864347908523709)
        ·
          refine ⟨14034497133324130465696391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37425325688864347908523709 14034497133324130465696391)
          ·
            refine ⟨21051745699986195698544587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14034497133324130465696391 21051745699986195698544587)
            ·
              refine ⟨31577618549979293547816881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21051745699986195698544587 31577618549979293547816881)
              ·
                refine ⟨23683213912484470160862661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31577618549979293547816881 23683213912484470160862661)
                ·
                  refine ⟨4440602608590838155161749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23683213912484470160862661 4440602608590838155161749)
                  ·
                    refine ⟨208153247277695538523207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4440602608590838155161749 208153247277695538523207)
                    ·
                      rfl

theorem cell23_1216131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 6].length) (baseStart_1216131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216131 prefixEnd_1216131 := by exact prefixLift 1216131
  have htrace : WordTrace (prefixWord ++ tailWord_1216131) baseStart_1216131 baseEnd_1216131 := by
    simpa [prefixWord, tailWord_1216131, baseEnd_1216131] using wordTrace_append hprefix tailTrace_1216131
  have hstable : (prefixWord ++ tailWord_1216131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216131).length < 2 ^ (prefixWord ++ tailWord_1216131).sum := by decide
  have hdescent : baseEnd_1216131 < baseStart_1216131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216212 : List Nat := [2, 4, 1, 3, 1, 1, 2, 4, 5]
def baseStart_1216212 : Nat := 118140960795 + 1216212 * 2 ^ 59
def prefixEnd_1216212 : Nat := 4983230072969 + 3 ^ 40 * 1216212 * 2
def baseEnd_1216212 : Nat := 69389037085122310961861

theorem tailTrace_1216212 : CollatzResearch.WordTrace tailWord_1216212 prefixEnd_1216212 69389037085122310961861 := by
  unfold tailWord_1216212
  simp only [CollatzResearch.WordTrace]
  refine ⟨22179447934939555658937445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29572597246586074211916593 22179447934939555658937445)
  ·
    refine ⟨4158646487801166686050771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22179447934939555658937445 4158646487801166686050771)
    ·
      refine ⟨6237969731701750029076157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4158646487801166686050771 6237969731701750029076157)
      ·
        refine ⟨2339238649388156260903559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6237969731701750029076157 2339238649388156260903559)
        ·
          refine ⟨3508857974082234391355339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339238649388156260903559 3508857974082234391355339)
          ·
            refine ⟨5263286961123351587033009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508857974082234391355339 5263286961123351587033009)
            ·
              refine ⟨3947465220842513690274757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5263286961123351587033009 3947465220842513690274757)
              ·
                refine ⟨740149728907971316926517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3947465220842513690274757 740149728907971316926517)
                ·
                  refine ⟨69389037085122310961861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 740149728907971316926517 69389037085122310961861)
                  ·
                    rfl

theorem cell23_1216212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_1216212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216212 prefixEnd_1216212 := by exact prefixLift 1216212
  have htrace : WordTrace (prefixWord ++ tailWord_1216212) baseStart_1216212 baseEnd_1216212 := by
    simpa [prefixWord, tailWord_1216212, baseEnd_1216212] using wordTrace_append hprefix tailTrace_1216212
  have hstable : (prefixWord ++ tailWord_1216212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216212).length < 2 ^ (prefixWord ++ tailWord_1216212).sum := by decide
  have hdescent : baseEnd_1216212 < baseStart_1216212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216228 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_1216228 : Nat := 118140960795 + 1216228 * 2 ^ 59
def prefixEnd_1216228 : Nat := 4983230072969 + 3 ^ 40 * 1216228 * 2
def baseEnd_1216228 : Nat := 624509549456572736056675

theorem tailTrace_1216228 : CollatzResearch.WordTrace tailWord_1216228 prefixEnd_1216228 624509549456572736056675 := by
  unfold tailWord_1216228
  simp only [CollatzResearch.WordTrace]
  refine ⟨22179739718910573025228669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29572986291880764033638225 22179739718910573025228669)
  ·
    refine ⟨8317402394591464884460751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22179739718910573025228669 8317402394591464884460751)
    ·
      refine ⟨12476103591887197326691127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8317402394591464884460751 12476103591887197326691127)
      ·
        refine ⟨18714155387830795990036691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12476103591887197326691127 18714155387830795990036691)
        ·
          refine ⟨28071233081746193985055037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18714155387830795990036691 28071233081746193985055037)
          ·
            refine ⟨10526712405654822744395639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28071233081746193985055037 10526712405654822744395639)
            ·
              refine ⟨15790068608482234116593459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10526712405654822744395639 15790068608482234116593459)
              ·
                refine ⟨23685102912723351174890189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15790068608482234116593459 23685102912723351174890189)
                ·
                  refine ⟨8881913592271256690583821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23685102912723351174890189 8881913592271256690583821)
                  ·
                    refine ⟨3330717597101721258968933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8881913592271256690583821 3330717597101721258968933)
                    ·
                      refine ⟨624509549456572736056675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3330717597101721258968933 624509549456572736056675)
                      ·
                        rfl

theorem cell23_1216228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_1216228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216228 prefixEnd_1216228 := by exact prefixLift 1216228
  have htrace : WordTrace (prefixWord ++ tailWord_1216228) baseStart_1216228 baseEnd_1216228 := by
    simpa [prefixWord, tailWord_1216228, baseEnd_1216228] using wordTrace_append hprefix tailTrace_1216228
  have hstable : (prefixWord ++ tailWord_1216228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216228).length < 2 ^ (prefixWord ++ tailWord_1216228).sum := by decide
  have hdescent : baseEnd_1216228 < baseStart_1216228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216238 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 2, 8]
def baseStart_1216238 : Nat := 118140960795 + 1216238 * 2 ^ 59
def prefixEnd_1216238 : Nat := 4983230072969 + 3 ^ 40 * 1216238 * 2
def baseEnd_1216238 : Nat := 208171561421039232310543

theorem tailTrace_1216238 : CollatzResearch.WordTrace tailWord_1216238 prefixEnd_1216238 208171561421039232310543 := by
  unfold tailWord_1216238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5544980520973114719790171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29573229445189945172214245 5544980520973114719790171)
  ·
    refine ⟨8317470781459672079685257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5544980520973114719790171 8317470781459672079685257)
    ·
      refine ⟨6238103086094754059763943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8317470781459672079685257 6238103086094754059763943)
      ·
        refine ⟨9357154629142131089645915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6238103086094754059763943 9357154629142131089645915)
        ·
          refine ⟨14035731943713196634468873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9357154629142131089645915 14035731943713196634468873)
          ·
            refine ⟨10526798957784897475851655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14035731943713196634468873 10526798957784897475851655)
            ·
              refine ⟨15790198436677346213777483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10526798957784897475851655 15790198436677346213777483)
              ·
                refine ⟨23685297655016019320666225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15790198436677346213777483 23685297655016019320666225)
                ·
                  refine ⟨17763973241262014490499669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23685297655016019320666225 17763973241262014490499669)
                  ·
                    refine ⟨208171561421039232310543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17763973241262014490499669 208171561421039232310543)
                    ·
                      rfl

theorem cell23_1216238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_1216238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216238 prefixEnd_1216238 := by exact prefixLift 1216238
  have htrace : WordTrace (prefixWord ++ tailWord_1216238) baseStart_1216238 baseEnd_1216238 := by
    simpa [prefixWord, tailWord_1216238, baseEnd_1216238] using wordTrace_append hprefix tailTrace_1216238
  have hstable : (prefixWord ++ tailWord_1216238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216238).length < 2 ^ (prefixWord ++ tailWord_1216238).sum := by decide
  have hdescent : baseEnd_1216238 < baseStart_1216238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216268 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 8]
def baseStart_1216268 : Nat := 118140960795 + 1216268 * 2 ^ 59
def prefixEnd_1216268 : Nat := 4983230072969 + 3 ^ 40 * 1216268 * 2
def baseEnd_1216268 : Nat := 69392232075861397728499

theorem tailTrace_1216268 : CollatzResearch.WordTrace tailWord_1216268 prefixEnd_1216268 69392232075861397728499 := by
  unfold tailWord_1216268
  simp only [CollatzResearch.WordTrace]
  refine ⟨22180469178838116440956729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29573958905117488587942305 22180469178838116440956729)
  ·
    refine ⟨16635351884128587330717547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22180469178838116440956729 16635351884128587330717547)
    ·
      refine ⟨24953027826192880996076321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16635351884128587330717547 24953027826192880996076321)
      ·
        refine ⟨18714770869644660747057241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24953027826192880996076321 18714770869644660747057241)
        ·
          refine ⟨14036078152233495560292931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18714770869644660747057241 14036078152233495560292931)
          ·
            refine ⟨21054117228350243340439397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14036078152233495560292931 21054117228350243340439397)
            ·
              refine ⟨3947646980315670626332387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21054117228350243340439397 3947646980315670626332387)
              ·
                refine ⟨5921470470473505939498581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947646980315670626332387 5921470470473505939498581)
                ·
                  refine ⟨69392232075861397728499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5921470470473505939498581 69392232075861397728499)
                  ·
                    rfl

theorem cell23_1216268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_1216268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216268 prefixEnd_1216268 := by exact prefixLift 1216268
  have htrace : WordTrace (prefixWord ++ tailWord_1216268) baseStart_1216268 baseEnd_1216268 := by
    simpa [prefixWord, tailWord_1216268, baseEnd_1216268] using wordTrace_append hprefix tailTrace_1216268
  have hstable : (prefixWord ++ tailWord_1216268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216268).length < 2 ^ (prefixWord ++ tailWord_1216268).sum := by decide
  have hdescent : baseEnd_1216268 < baseStart_1216268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216329 : List Nat := [1, 2, 1, 1, 2, 4, 3, 4, 1, 1, 3]
def baseStart_1216329 : Nat := 118140960795 + 1216329 * 2 ^ 59
def prefixEnd_1216329 : Nat := 4983230072969 + 3 ^ 40 * 1216329 * 2
def baseEnd_1216329 : Nat := 624561411002676840893711

theorem tailTrace_1216329 : CollatzResearch.WordTrace tailWord_1216329 prefixEnd_1216329 624561411002676840893711 := by
  unfold tailWord_1216329
  simp only [CollatzResearch.WordTrace]
  refine ⟨44363163210455240299884041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29575442140303493533256027 44363163210455240299884041)
  ·
    refine ⟨33272372407841430224913031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44363163210455240299884041 33272372407841430224913031)
    ·
      refine ⟨49908558611762145337369547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33272372407841430224913031 49908558611762145337369547)
      ·
        refine ⟨74862837917643218006054321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49908558611762145337369547 74862837917643218006054321)
        ·
          refine ⟨56147128438232413504540741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74862837917643218006054321 56147128438232413504540741)
          ·
            refine ⟨10527586582168577532101389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56147128438232413504540741 10527586582168577532101389)
            ·
              refine ⟨3947844968313216574538021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10527586582168577532101389 3947844968313216574538021)
              ·
                refine ⟨740220931558728107725879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3947844968313216574538021 740220931558728107725879)
                ·
                  refine ⟨1110331397338092161588819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740220931558728107725879 1110331397338092161588819)
                  ·
                    refine ⟨1665497096007138242383229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1110331397338092161588819 1665497096007138242383229)
                    ·
                      refine ⟨624561411002676840893711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1665497096007138242383229 624561411002676840893711)
                      ·
                        rfl

theorem cell23_1216329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 4, 1, 1, 3].length) (baseStart_1216329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216329 prefixEnd_1216329 := by exact prefixLift 1216329
  have htrace : WordTrace (prefixWord ++ tailWord_1216329) baseStart_1216329 baseEnd_1216329 := by
    simpa [prefixWord, tailWord_1216329, baseEnd_1216329] using wordTrace_append hprefix tailTrace_1216329
  have hstable : (prefixWord ++ tailWord_1216329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216329).length < 2 ^ (prefixWord ++ tailWord_1216329).sum := by decide
  have hdescent : baseEnd_1216329 < baseStart_1216329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216345 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 1, 6]
def baseStart_1216345 : Nat := 118140960795 + 1216345 * 2 ^ 59
def prefixEnd_1216345 : Nat := 4983230072969 + 3 ^ 40 * 1216345 * 2
def baseEnd_1216345 : Nat := 208189875564382926097879

theorem tailTrace_1216345 : CollatzResearch.WordTrace tailWord_1216345 prefixEnd_1216345 208189875564382926097879 := by
  unfold tailWord_1216345
  simp only [CollatzResearch.WordTrace]
  refine ⟨44363746778397275032466489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29575831185598183354977659 44363746778397275032466489)
  ·
    refine ⟨33272810083797956274349867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44363746778397275032466489 33272810083797956274349867)
    ·
      refine ⟨49909215125696934411524801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33272810083797956274349867 49909215125696934411524801)
      ·
        refine ⟨37431911344272700808643601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49909215125696934411524801 37431911344272700808643601)
        ·
          refine ⟨28073933508204525606482701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37431911344272700808643601 28073933508204525606482701)
          ·
            refine ⟨10527725065576697102431013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28073933508204525606482701 10527725065576697102431013)
            ·
              refine ⟨1973948449795630706705815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10527725065576697102431013 1973948449795630706705815)
              ·
                refine ⟨2960922674693446060058723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973948449795630706705815 2960922674693446060058723)
                ·
                  refine ⟨4441384012040169090088085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2960922674693446060058723 4441384012040169090088085)
                  ·
                    refine ⟨208189875564382926097879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4441384012040169090088085 208189875564382926097879)
                    ·
                      rfl

theorem cell23_1216345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_1216345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216345 prefixEnd_1216345 := by exact prefixLift 1216345
  have htrace : WordTrace (prefixWord ++ tailWord_1216345) baseStart_1216345 baseEnd_1216345 := by
    simpa [prefixWord, tailWord_1216345, baseEnd_1216345] using wordTrace_append hprefix tailTrace_1216345
  have hstable : (prefixWord ++ tailWord_1216345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216345).length < 2 ^ (prefixWord ++ tailWord_1216345).sum := by decide
  have hdescent : baseEnd_1216345 < baseStart_1216345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216356 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 2, 3, 2]
def baseStart_1216356 : Nat := 118140960795 + 1216356 * 2 ^ 59
def prefixEnd_1216356 : Nat := 4983230072969 + 3 ^ 40 * 1216356 * 2
def baseEnd_1216356 : Nat := 624575274980348235256087

theorem tailTrace_1216356 : CollatzResearch.WordTrace tailWord_1216356 prefixEnd_1216356 624575274980348235256087 := by
  unfold tailWord_1216356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22182073990678711955558461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29576098654238282607411281 22182073990678711955558461)
  ·
    refine ⟨8318277746504516983334423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22182073990678711955558461 8318277746504516983334423)
    ·
      refine ⟨12477416619756775475001635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8318277746504516983334423 12477416619756775475001635)
      ·
        refine ⟨18716124929635163212502453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12477416619756775475001635 18716124929635163212502453)
        ·
          refine ⟨1754636712153296551172105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18716124929635163212502453 1754636712153296551172105)
          ·
            refine ⟨1315977534114972413379079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1754636712153296551172105 1315977534114972413379079)
            ·
              refine ⟨1973966301172458620068619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315977534114972413379079 1973966301172458620068619)
              ·
                refine ⟨2960949451758687930102929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973966301172458620068619 2960949451758687930102929)
                ·
                  refine ⟨2220712088819015947577197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2960949451758687930102929 2220712088819015947577197)
                  ·
                    refine ⟨832767033307130980341449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2220712088819015947577197 832767033307130980341449)
                    ·
                      refine ⟨624575274980348235256087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832767033307130980341449 624575274980348235256087)
                      ·
                        rfl

theorem cell23_1216356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_1216356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216356 prefixEnd_1216356 := by exact prefixLift 1216356
  have htrace : WordTrace (prefixWord ++ tailWord_1216356) baseStart_1216356 baseEnd_1216356 := by
    simpa [prefixWord, tailWord_1216356, baseEnd_1216356] using wordTrace_append hprefix tailTrace_1216356
  have hstable : (prefixWord ++ tailWord_1216356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216356).length < 2 ^ (prefixWord ++ tailWord_1216356).sum := by decide
  have hdescent : baseEnd_1216356 < baseStart_1216356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216366 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_1216366 : Nat := 118140960795 + 1216366 * 2 ^ 59
def prefixEnd_1216366 : Nat := 4983230072969 + 3 ^ 40 * 1216366 * 2
def baseEnd_1216366 : Nat := 208193469928964398710347

theorem tailTrace_1216366 : CollatzResearch.WordTrace tailWord_1216366 prefixEnd_1216366 208193469928964398710347 := by
  unfold tailWord_1216366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5545564088915149452372619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29576341807547463745987301 5545564088915149452372619)
  ·
    refine ⟨8318346133372724178558929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5545564088915149452372619 8318346133372724178558929)
    ·
      refine ⟨6238759600029543133919197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8318346133372724178558929 6238759600029543133919197)
      ·
        refine ⟨2339534850011078675219699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6238759600029543133919197 2339534850011078675219699)
        ·
          refine ⟨3509302275016618012829549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339534850011078675219699 3509302275016618012829549)
          ·
            refine ⟨1315988353131231754811081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3509302275016618012829549 1315988353131231754811081)
            ·
              refine ⟨986991264848423816108311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315988353131231754811081 986991264848423816108311)
              ·
                refine ⟨1480486897272635724162467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986991264848423816108311 1480486897272635724162467)
                ·
                  refine ⟨2220730345908953586243701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480486897272635724162467 2220730345908953586243701)
                  ·
                    refine ⟨208193469928964398710347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2220730345908953586243701 208193469928964398710347)
                    ·
                      rfl

theorem cell23_1216366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_1216366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216366 prefixEnd_1216366 := by exact prefixLift 1216366
  have htrace : WordTrace (prefixWord ++ tailWord_1216366) baseStart_1216366 baseEnd_1216366 := by
    simpa [prefixWord, tailWord_1216366, baseEnd_1216366] using wordTrace_append hprefix tailTrace_1216366
  have hstable : (prefixWord ++ tailWord_1216366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216366).length < 2 ^ (prefixWord ++ tailWord_1216366).sum := by decide
  have hdescent : baseEnd_1216366 < baseStart_1216366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216442 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2]
def baseStart_1216442 : Nat := 118140960795 + 1216442 * 2 ^ 59
def prefixEnd_1216442 : Nat := 4983230072969 + 3 ^ 40 * 1216442 * 2
def baseEnd_1216442 : Nat := 624619434316634898780691

theorem tailTrace_1216442 : CollatzResearch.WordTrace tailWord_1216442 prefixEnd_1216442 624619434316634898780691 := by
  unfold tailWord_1216442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11091821164761465149686895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29578189772697240399165053 11091821164761465149686895)
  ·
    refine ⟨16637731747142197724530343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11091821164761465149686895 16637731747142197724530343)
    ·
      refine ⟨24956597620713296586795515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16637731747142197724530343 24956597620713296586795515)
      ·
        refine ⟨37434896431069944880193273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24956597620713296586795515 37434896431069944880193273)
        ·
          refine ⟨28076172323302458660144955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37434896431069944880193273 28076172323302458660144955)
          ·
            refine ⟨42114258484953687990217433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28076172323302458660144955 42114258484953687990217433)
            ·
              refine ⟨31585693863715265992663075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42114258484953687990217433 31585693863715265992663075)
              ·
                refine ⟨47378540795572898988994613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31585693863715265992663075 47378540795572898988994613)
                ·
                  refine ⟨4441738199584959280218245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47378540795572898988994613 4441738199584959280218245)
                  ·
                    refine ⟨832825912422179865040921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4441738199584959280218245 832825912422179865040921)
                    ·
                      refine ⟨624619434316634898780691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832825912422179865040921 624619434316634898780691)
                      ·
                        rfl

theorem cell23_1216442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_1216442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216442 prefixEnd_1216442 := by exact prefixLift 1216442
  have htrace : WordTrace (prefixWord ++ tailWord_1216442) baseStart_1216442 baseEnd_1216442 := by
    simpa [prefixWord, tailWord_1216442, baseEnd_1216442] using wordTrace_append hprefix tailTrace_1216442
  have hstable : (prefixWord ++ tailWord_1216442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216442).length < 2 ^ (prefixWord ++ tailWord_1216442).sum := by decide
  have hdescent : baseEnd_1216442 < baseStart_1216442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216455 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1216455 : Nat := 118140960795 + 1216455 * 2 ^ 59
def prefixEnd_1216455 : Nat := 4983230072969 + 3 ^ 40 * 1216455 * 2
def baseEnd_1216455 : Nat := 624626109565143347918131

theorem tailTrace_1216455 : CollatzResearch.WordTrace tailWord_1216455 prefixEnd_1216455 624626109565143347918131 := by
  unfold tailWord_1216455
  simp only [CollatzResearch.WordTrace]
  refine ⟨44367758807998763818970819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29578505871999175879313879 44367758807998763818970819)
  ·
    refine ⟨66551638211998145728456229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44367758807998763818970819 66551638211998145728456229)
    ·
      refine ⟨12478432164749652324085543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66551638211998145728456229 12478432164749652324085543)
      ·
        refine ⟨18717648247124478486128315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12478432164749652324085543 18717648247124478486128315)
        ·
          refine ⟨28076472370686717729192473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18717648247124478486128315 28076472370686717729192473)
          ·
            refine ⟨21057354278015038296894355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28076472370686717729192473 21057354278015038296894355)
            ·
              refine ⟨31586031417022557445341533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21057354278015038296894355 31586031417022557445341533)
              ·
                refine ⟨11844761781383459042003075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31586031417022557445341533 11844761781383459042003075)
                ·
                  refine ⟨17767142672075188563004613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11844761781383459042003075 17767142672075188563004613)
                  ·
                    refine ⟨3331339251014097855563365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17767142672075188563004613 3331339251014097855563365)
                    ·
                      refine ⟨624626109565143347918131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3331339251014097855563365 624626109565143347918131)
                      ·
                        rfl

theorem cell23_1216455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1216455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216455 prefixEnd_1216455 := by exact prefixLift 1216455
  have htrace : WordTrace (prefixWord ++ tailWord_1216455) baseStart_1216455 baseEnd_1216455 := by
    simpa [prefixWord, tailWord_1216455, baseEnd_1216455] using wordTrace_append hprefix tailTrace_1216455
  have hstable : (prefixWord ++ tailWord_1216455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216455).length < 2 ^ (prefixWord ++ tailWord_1216455).sum := by decide
  have hdescent : baseEnd_1216455 < baseStart_1216455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216549 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 2, 4, 2]
def baseStart_1216549 : Nat := 118140960795 + 1216549 * 2 ^ 59
def prefixEnd_1216549 : Nat := 4983230072969 + 3 ^ 40 * 1216549 * 2
def baseEnd_1216549 : Nat := 624674376746665980142699

theorem tailTrace_1216549 : CollatzResearch.WordTrace tailWord_1216549 prefixEnd_1216549 624674376746665980142699 := by
  unfold tailWord_1216549
  simp only [CollatzResearch.WordTrace]
  refine ⟨44371187269658217872892701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29580791513105478581928467 44371187269658217872892701)
  ·
    refine ⟨16639195226121831702334763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44371187269658217872892701 16639195226121831702334763)
    ·
      refine ⟨24958792839182747553502145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16639195226121831702334763 24958792839182747553502145)
      ·
        refine ⟨18719094629387060665126609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24958792839182747553502145 18719094629387060665126609)
        ·
          refine ⟨14039320972040295498844957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18719094629387060665126609 14039320972040295498844957)
          ·
            refine ⟨5264745364515110812066859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14039320972040295498844957 5264745364515110812066859)
            ·
              refine ⟨7897118046772666218100289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5264745364515110812066859 7897118046772666218100289)
              ·
                refine ⟨5922838535079499663575217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7897118046772666218100289 5922838535079499663575217)
                ·
                  refine ⟨4442128901309624747681413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5922838535079499663575217 4442128901309624747681413)
                  ·
                    refine ⟨832899168995554640190265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4442128901309624747681413 832899168995554640190265)
                    ·
                      refine ⟨624674376746665980142699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832899168995554640190265 624674376746665980142699)
                      ·
                        rfl

theorem cell23_1216549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_1216549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216549 prefixEnd_1216549 := by exact prefixLift 1216549
  have htrace : WordTrace (prefixWord ++ tailWord_1216549) baseStart_1216549 baseEnd_1216549 := by
    simpa [prefixWord, tailWord_1216549, baseEnd_1216549] using wordTrace_append hprefix tailTrace_1216549
  have hstable : (prefixWord ++ tailWord_1216549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216549).length < 2 ^ (prefixWord ++ tailWord_1216549).sum := by decide
  have hdescent : baseEnd_1216549 < baseStart_1216549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216566 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_1216566 : Nat := 118140960795 + 1216566 * 2 ^ 59
def prefixEnd_1216566 : Nat := 4983230072969 + 3 ^ 40 * 1216566 * 2
def baseEnd_1216566 : Nat := 624683105917792413630121

theorem tailTrace_1216566 : CollatzResearch.WordTrace tailWord_1216566 prefixEnd_1216566 624683105917792413630121 := by
  unfold tailWord_1216566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773237956912289361016347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29581204873731086517507701 2773237956912289361016347)
  ·
    refine ⟨4159856935368434041524521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2773237956912289361016347 4159856935368434041524521)
    ·
      refine ⟨3119892701526325531143391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4159856935368434041524521 3119892701526325531143391)
      ·
        refine ⟨4679839052289488296715087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3119892701526325531143391 4679839052289488296715087)
        ·
          refine ⟨7019758578434232445072631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4679839052289488296715087 7019758578434232445072631)
          ·
            refine ⟨10529637867651348667608947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7019758578434232445072631 10529637867651348667608947)
            ·
              refine ⟨15794456801477023001413421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10529637867651348667608947 15794456801477023001413421)
              ·
                refine ⟨5922921300553883625530033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15794456801477023001413421 5922921300553883625530033)
                ·
                  refine ⟨4442190975415412719147525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5922921300553883625530033 4442190975415412719147525)
                  ·
                    refine ⟨832910807890389884840161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4442190975415412719147525 832910807890389884840161)
                    ·
                      refine ⟨624683105917792413630121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 832910807890389884840161 624683105917792413630121)
                      ·
                        rfl

theorem cell23_1216566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_1216566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216566 prefixEnd_1216566 := by exact prefixLift 1216566
  have htrace : WordTrace (prefixWord ++ tailWord_1216566) baseStart_1216566 baseEnd_1216566 := by
    simpa [prefixWord, tailWord_1216566, baseEnd_1216566] using wordTrace_append hprefix tailTrace_1216566
  have hstable : (prefixWord ++ tailWord_1216566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216566).length < 2 ^ (prefixWord ++ tailWord_1216566).sum := by decide
  have hdescent : baseEnd_1216566 < baseStart_1216566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216599 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 3]
def baseStart_1216599 : Nat := 118140960795 + 1216599 * 2 ^ 59
def prefixEnd_1216599 : Nat := 4983230072969 + 3 ^ 40 * 1216599 * 2
def baseEnd_1216599 : Nat := 624700050779390784517469

theorem tailTrace_1216599 : CollatzResearch.WordTrace tailWord_1216599 prefixEnd_1216599 624700050779390784517469 := by
  unfold tailWord_1216599
  simp only [CollatzResearch.WordTrace]
  refine ⟨44373010919477076412212851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29582007279651384274808567 44373010919477076412212851)
  ·
    refine ⟨66559516379215614618319277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44373010919477076412212851 66559516379215614618319277)
    ·
      refine ⟨24959818642205855481869729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66559516379215614618319277 24959818642205855481869729)
      ·
        refine ⟨18719863981654391611402297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24959818642205855481869729 18719863981654391611402297)
        ·
          refine ⟨14039897986240793708551723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18719863981654391611402297 14039897986240793708551723)
          ·
            refine ⟨21059846979361190562827585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14039897986240793708551723 21059846979361190562827585)
            ·
              refine ⟨15794885234520892922120689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21059846979361190562827585 15794885234520892922120689)
              ·
                refine ⟨11846163925890669691590517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15794885234520892922120689 11846163925890669691590517)
                ·
                  refine ⟨1110577868052250283586611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11846163925890669691590517 1110577868052250283586611)
                  ·
                    refine ⟨1665866802078375425379917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1110577868052250283586611 1665866802078375425379917)
                    ·
                      refine ⟨624700050779390784517469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1665866802078375425379917 624700050779390784517469)
                      ·
                        rfl

theorem cell23_1216599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_1216599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216599 prefixEnd_1216599 := by exact prefixLift 1216599
  have htrace : WordTrace (prefixWord ++ tailWord_1216599) baseStart_1216599 baseEnd_1216599 := by
    simpa [prefixWord, tailWord_1216599, baseEnd_1216599] using wordTrace_append hprefix tailTrace_1216599
  have hstable : (prefixWord ++ tailWord_1216599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216599).length < 2 ^ (prefixWord ++ tailWord_1216599).sum := by decide
  have hdescent : baseEnd_1216599 < baseStart_1216599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216610 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1216610 : Nat := 118140960795 + 1216610 * 2 ^ 59
def prefixEnd_1216610 : Nat := 4983230072969 + 3 ^ 40 * 1216610 * 2
def baseEnd_1216610 : Nat := 208235233022196747159973

theorem tailTrace_1216610 : CollatzResearch.WordTrace tailWord_1216610 prefixEnd_1216610 208235233022196747159973 := by
  unfold tailWord_1216610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11093353030609306322715821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29582274748291483527242189 11093353030609306322715821)
  ·
    refine ⟨4160007386478489871018433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11093353030609306322715821 4160007386478489871018433)
    ·
      refine ⟨3120005539858867403263825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4160007386478489871018433 3120005539858867403263825)
      ·
        refine ⟨2340004154894150552447869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3120005539858867403263825 2340004154894150552447869)
        ·
          refine ⟨877501558085306457167951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2340004154894150552447869 877501558085306457167951)
          ·
            refine ⟨1316252337127959685751927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877501558085306457167951 1316252337127959685751927)
            ·
              refine ⟨1974378505691939528627891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316252337127959685751927 1974378505691939528627891)
              ·
                refine ⟨2961567758537909292941837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1974378505691939528627891 2961567758537909292941837)
                ·
                  refine ⟨1110587909451715984853189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2961567758537909292941837 1110587909451715984853189)
                  ·
                    refine ⟨208235233022196747159973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1110587909451715984853189 208235233022196747159973)
                    ·
                      rfl

theorem cell23_1216610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1216610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216610 prefixEnd_1216610 := by exact prefixLift 1216610
  have htrace : WordTrace (prefixWord ++ tailWord_1216610) baseStart_1216610 baseEnd_1216610 := by
    simpa [prefixWord, tailWord_1216610, baseEnd_1216610] using wordTrace_append hprefix tailTrace_1216610
  have hstable : (prefixWord ++ tailWord_1216610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216610).length < 2 ^ (prefixWord ++ tailWord_1216610).sum := by decide
  have hdescent : baseEnd_1216610 < baseStart_1216610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216632 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 1, 6]
def baseStart_1216632 : Nat := 118140960795 + 1216632 * 2 ^ 59
def prefixEnd_1216632 : Nat := 4983230072969 + 3 ^ 40 * 1216632 * 2
def baseEnd_1216632 : Nat := 208238998546996385134939

theorem tailTrace_1216632 : CollatzResearch.WordTrace tailWord_1216632 prefixEnd_1216632 208238998546996385134939 := by
  unfold tailWord_1216632
  simp only [CollatzResearch.WordTrace]
  refine ⟨22187107264178761524082075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29582809685571682032109433 22187107264178761524082075)
  ·
    refine ⟨33280660896268142286123113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22187107264178761524082075 33280660896268142286123113)
    ·
      refine ⟨24960495672201106714592335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33280660896268142286123113 24960495672201106714592335)
      ·
        refine ⟨37440743508301660071888503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24960495672201106714592335 37440743508301660071888503)
        ·
          refine ⟨56161115262452490107832755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37440743508301660071888503 56161115262452490107832755)
          ·
            refine ⟨84241672893678735161749133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56161115262452490107832755 84241672893678735161749133)
            ·
              refine ⟨31590627335129525685655925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84241672893678735161749133 31590627335129525685655925)
              ·
                refine ⟨2961621312668393033030243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31590627335129525685655925 2961621312668393033030243)
                ·
                  refine ⟨4442431969002589549545365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961621312668393033030243 4442431969002589549545365)
                  ·
                    refine ⟨208238998546996385134939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4442431969002589549545365 208238998546996385134939)
                    ·
                      rfl

theorem cell23_1216632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_1216632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216632 prefixEnd_1216632 := by exact prefixLift 1216632
  have htrace : WordTrace (prefixWord ++ tailWord_1216632) baseStart_1216632 baseEnd_1216632 := by
    simpa [prefixWord, tailWord_1216632, baseEnd_1216632] using wordTrace_append hprefix tailTrace_1216632
  have hstable : (prefixWord ++ tailWord_1216632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216632).length < 2 ^ (prefixWord ++ tailWord_1216632).sum := by decide
  have hdescent : baseEnd_1216632 < baseStart_1216632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216636 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_1216636 : Nat := 118140960795 + 1216636 * 2 ^ 59
def prefixEnd_1216636 : Nat := 4983230072969 + 3 ^ 40 * 1216636 * 2
def baseEnd_1216636 : Nat := 208239683187869046584933

theorem tailTrace_1216636 : CollatzResearch.WordTrace tailWord_1216636 prefixEnd_1216636 208239683187869046584933 := by
  unfold tailWord_1216636
  simp only [CollatzResearch.WordTrace]
  refine ⟨22187180210171515865654881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29582906946895354487539841 22187180210171515865654881)
  ·
    refine ⟨16640385157628636899241161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22187180210171515865654881 16640385157628636899241161)
    ·
      refine ⟨12480288868221477674430871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16640385157628636899241161 12480288868221477674430871)
      ·
        refine ⟨18720433302332216511646307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12480288868221477674430871 18720433302332216511646307)
        ·
          refine ⟨28080649953498324767469461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18720433302332216511646307 28080649953498324767469461)
          ·
            refine ⟨1316280466570233973475131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28080649953498324767469461 1316280466570233973475131)
            ·
              refine ⟨1974420699855350960212697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316280466570233973475131 1974420699855350960212697)
              ·
                refine ⟨1480815524891513220159523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974420699855350960212697 1480815524891513220159523)
                ·
                  refine ⟨2221223287337269830239285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480815524891513220159523 2221223287337269830239285)
                  ·
                    refine ⟨208239683187869046584933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2221223287337269830239285 208239683187869046584933)
                    ·
                      rfl

theorem cell23_1216636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_1216636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216636 prefixEnd_1216636 := by exact prefixLift 1216636
  have htrace : WordTrace (prefixWord ++ tailWord_1216636) baseStart_1216636 baseEnd_1216636 := by
    simpa [prefixWord, tailWord_1216636, baseEnd_1216636] using wordTrace_append hprefix tailTrace_1216636
  have hstable : (prefixWord ++ tailWord_1216636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216636).length < 2 ^ (prefixWord ++ tailWord_1216636).sum := by decide
  have hdescent : baseEnd_1216636 < baseStart_1216636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216656 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 1, 1, 4]
def baseStart_1216656 : Nat := 118140960795 + 1216656 * 2 ^ 59
def prefixEnd_1216656 : Nat := 4983230072969 + 3 ^ 40 * 1216656 * 2
def baseEnd_1216656 : Nat := 624729319176697061504707

theorem tailTrace_1216656 : CollatzResearch.WordTrace tailWord_1216656 prefixEnd_1216656 624729319176697061504707 := by
  unfold tailWord_1216656
  simp only [CollatzResearch.WordTrace]
  refine ⟨22187544940135287573518911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29583393253513716764691881 22187544940135287573518911)
  ·
    refine ⟨33281317410202931360278367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22187544940135287573518911 33281317410202931360278367)
    ·
      refine ⟨49921976115304397040417551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33281317410202931360278367 49921976115304397040417551)
      ·
        refine ⟨74882964172956595560626327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49921976115304397040417551 74882964172956595560626327)
        ·
          refine ⟨112324446259434893340939491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74882964172956595560626327 112324446259434893340939491)
          ·
            refine ⟨168486669389152340011409237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112324446259434893340939491 168486669389152340011409237)
            ·
              refine ⟨987226578452064492254351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 168486669389152340011409237 987226578452064492254351)
              ·
                refine ⟨1480839867678096738381527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987226578452064492254351 1480839867678096738381527)
                ·
                  refine ⟨2221259801517145107572291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1480839867678096738381527 2221259801517145107572291)
                  ·
                    refine ⟨3331889702275717661358437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2221259801517145107572291 3331889702275717661358437)
                    ·
                      refine ⟨624729319176697061504707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3331889702275717661358437 624729319176697061504707)
                      ·
                        rfl

theorem cell23_1216656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 1, 4].length) (baseStart_1216656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216656 prefixEnd_1216656 := by exact prefixLift 1216656
  have htrace : WordTrace (prefixWord ++ tailWord_1216656) baseStart_1216656 baseEnd_1216656 := by
    simpa [prefixWord, tailWord_1216656, baseEnd_1216656] using wordTrace_append hprefix tailTrace_1216656
  have hstable : (prefixWord ++ tailWord_1216656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216656).length < 2 ^ (prefixWord ++ tailWord_1216656).sum := by decide
  have hdescent : baseEnd_1216656 < baseStart_1216656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216766 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1216766 : Nat := 118140960795 + 1216766 * 2 ^ 59
def prefixEnd_1216766 : Nat := 4983230072969 + 3 ^ 40 * 1216766 * 2
def baseEnd_1216766 : Nat := 624785802048691631129201

theorem tailTrace_1216766 : CollatzResearch.WordTrace tailWord_1216766 prefixEnd_1216766 624785802048691631129201 := by
  unfold tailWord_1216766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5547387738734007991692769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29586067939914709289028101 5547387738734007991692769)
  ·
    refine ⟨4160540804050505993769577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5547387738734007991692769 4160540804050505993769577)
    ·
      refine ⟨3120405603037879495327183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4160540804050505993769577 3120405603037879495327183)
      ·
        refine ⟨4680608404556819242990775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3120405603037879495327183 4680608404556819242990775)
        ·
          refine ⟨7020912606835228864486163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4680608404556819242990775 7020912606835228864486163)
          ·
            refine ⟨10531368910252843296729245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7020912606835228864486163 10531368910252843296729245)
            ·
              refine ⟨3949263341344816236273467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10531368910252843296729245 3949263341344816236273467)
              ·
                refine ⟨5923895012017224354410201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3949263341344816236273467 5923895012017224354410201)
                ·
                  refine ⟨4442921259012918265807651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5923895012017224354410201 4442921259012918265807651)
                  ·
                    refine ⟨6664381888519377398711477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4442921259012918265807651 6664381888519377398711477)
                    ·
                      refine ⟨624785802048691631129201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6664381888519377398711477 624785802048691631129201)
                      ·
                        rfl

theorem cell23_1216766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1216766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216766 prefixEnd_1216766 := by exact prefixLift 1216766
  have htrace : WordTrace (prefixWord ++ tailWord_1216766) baseStart_1216766 baseEnd_1216766 := by
    simpa [prefixWord, tailWord_1216766, baseEnd_1216766] using wordTrace_append hprefix tailTrace_1216766
  have hstable : (prefixWord ++ tailWord_1216766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216766).length < 2 ^ (prefixWord ++ tailWord_1216766).sum := by decide
  have hdescent : baseEnd_1216766 < baseStart_1216766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216797 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_1216797 : Nat := 118140960795 + 1216797 * 2 ^ 59
def prefixEnd_1216797 : Nat := 4983230072969 + 3 ^ 40 * 1216797 * 2
def baseEnd_1216797 : Nat := 624801719948981009841559

theorem tailTrace_1216797 : CollatzResearch.WordTrace tailWord_1216797 prefixEnd_1216797 624801719948981009841559 := by
  unfold tailWord_1216797
  simp only [CollatzResearch.WordTrace]
  refine ⟨44380232572759756227920645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29586821715173170818613763 44380232572759756227920645)
  ·
    refine ⟨8321293607392454292735121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44380232572759756227920645 8321293607392454292735121)
    ·
      refine ⟨6240970205544340719551341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8321293607392454292735121 6240970205544340719551341)
      ·
        refine ⟨2340363827079127769831753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6240970205544340719551341 2340363827079127769831753)
        ·
          refine ⟨1755272870309345827373815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2340363827079127769831753 1755272870309345827373815)
          ·
            refine ⟨2632909305464018741060723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755272870309345827373815 2632909305464018741060723)
            ·
              refine ⟨3949363958196028111591085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632909305464018741060723 3949363958196028111591085)
              ·
                refine ⟨1481011484323510541846657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3949363958196028111591085 1481011484323510541846657)
                ·
                  refine ⟨1110758613242632906384993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1481011484323510541846657 1110758613242632906384993)
                  ·
                    refine ⟨833068959931974679788745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1110758613242632906384993 833068959931974679788745)
                    ·
                      refine ⟨624801719948981009841559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833068959931974679788745 624801719948981009841559)
                      ·
                        rfl

theorem cell23_1216797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_1216797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216797 prefixEnd_1216797 := by exact prefixLift 1216797
  have htrace : WordTrace (prefixWord ++ tailWord_1216797) baseStart_1216797 baseEnd_1216797 := by
    simpa [prefixWord, tailWord_1216797, baseEnd_1216797] using wordTrace_append hprefix tailTrace_1216797
  have hstable : (prefixWord ++ tailWord_1216797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216797).length < 2 ^ (prefixWord ++ tailWord_1216797).sum := by decide
  have hdescent : baseEnd_1216797 < baseStart_1216797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216839 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1216839 : Nat := 118140960795 + 1216839 * 2 ^ 59
def prefixEnd_1216839 : Nat := 4983230072969 + 3 ^ 40 * 1216839 * 2
def baseEnd_1216839 : Nat := 624823286136469845516365

theorem tailTrace_1216839 : CollatzResearch.WordTrace tailWord_1216839 prefixEnd_1216839 624823286136469845516365 := by
  unfold tailWord_1216839
  simp only [CollatzResearch.WordTrace]
  refine ⟨44381764438607597400949571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29587842959071731600633047 44381764438607597400949571)
  ·
    refine ⟨66572646657911396101424357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44381764438607597400949571 66572646657911396101424357)
    ·
      refine ⟨12482371248358386769017067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66572646657911396101424357 12482371248358386769017067)
      ·
        refine ⟨18723556872537580153525601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12482371248358386769017067 18723556872537580153525601)
        ·
          refine ⟨14042667654403185115144201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18723556872537580153525601 14042667654403185115144201)
          ·
            refine ⟨10532000740802388836358151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14042667654403185115144201 10532000740802388836358151)
            ·
              refine ⟨15798001111203583254537227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10532000740802388836358151 15798001111203583254537227)
              ·
                refine ⟨23697001666805374881805841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15798001111203583254537227 23697001666805374881805841)
                ·
                  refine ⟨17772751250104031161354381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23697001666805374881805841 17772751250104031161354381)
                  ·
                    refine ⟨6664781718789011685507893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17772751250104031161354381 6664781718789011685507893)
                    ·
                      refine ⟨624823286136469845516365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6664781718789011685507893 624823286136469845516365)
                      ·
                        rfl

theorem cell23_1216839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1216839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216839 prefixEnd_1216839 := by exact prefixLift 1216839
  have htrace : WordTrace (prefixWord ++ tailWord_1216839) baseStart_1216839 baseEnd_1216839 := by
    simpa [prefixWord, tailWord_1216839, baseEnd_1216839] using wordTrace_append hprefix tailTrace_1216839
  have hstable : (prefixWord ++ tailWord_1216839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216839).length < 2 ^ (prefixWord ++ tailWord_1216839).sum := by decide
  have hdescent : baseEnd_1216839 < baseStart_1216839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216880 : List Nat := [2, 1, 1, 1, 4, 4, 2, 3, 1, 4]
def baseStart_1216880 : Nat := 118140960795 + 1216880 * 2 ^ 59
def prefixEnd_1216880 : Nat := 4983230072969 + 3 ^ 40 * 1216880 * 2
def baseEnd_1216880 : Nat := 208281446281101395034559

theorem tailTrace_1216880 : CollatzResearch.WordTrace tailWord_1216880 prefixEnd_1216880 208281446281101395034559 := by
  unfold tailWord_1216880
  simp only [CollatzResearch.WordTrace]
  refine ⟨22191629915729530701596047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29588839887639374268794729 22191629915729530701596047)
  ·
    refine ⟨33287444873594296052394071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22191629915729530701596047 33287444873594296052394071)
    ·
      refine ⟨49931167310391444078591107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33287444873594296052394071 49931167310391444078591107)
      ·
        refine ⟨74896750965587166117886661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49931167310391444078591107 74896750965587166117886661)
        ·
          refine ⟨14043140806047593647103749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74896750965587166117886661 14043140806047593647103749)
          ·
            refine ⟨2633088901133923808831953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14043140806047593647103749 2633088901133923808831953)
            ·
              refine ⟨1974816675850442856623965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2633088901133923808831953 1974816675850442856623965)
              ·
                refine ⟨740556253443916071233987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1974816675850442856623965 740556253443916071233987)
                ·
                  refine ⟨1110834380165874106850981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740556253443916071233987 1110834380165874106850981)
                  ·
                    refine ⟨208281446281101395034559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1110834380165874106850981 208281446281101395034559)
                    ·
                      rfl

theorem cell23_1216880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 4].length) (baseStart_1216880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216880 prefixEnd_1216880 := by exact prefixLift 1216880
  have htrace : WordTrace (prefixWord ++ tailWord_1216880) baseStart_1216880 baseEnd_1216880 := by
    simpa [prefixWord, tailWord_1216880, baseEnd_1216880] using wordTrace_append hprefix tailTrace_1216880
  have hstable : (prefixWord ++ tailWord_1216880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216880).length < 2 ^ (prefixWord ++ tailWord_1216880).sum := by decide
  have hdescent : baseEnd_1216880 < baseStart_1216880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216893 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 6]
def baseStart_1216893 : Nat := 118140960795 + 1216893 * 2 ^ 59
def prefixEnd_1216893 : Nat := 4983230072969 + 3 ^ 40 * 1216893 * 2
def baseEnd_1216893 : Nat := 69427890454645848249013

theorem tailTrace_1216893 : CollatzResearch.WordTrace tailWord_1216893 prefixEnd_1216893 69427890454645848249013 := by
  unfold tailWord_1216893
  simp only [CollatzResearch.WordTrace]
  refine ⟨44383733980411964623415333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29589155986941309748943555 44383733980411964623415333)
  ·
    refine ⟨8321950121327243366890375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44383733980411964623415333 8321950121327243366890375)
    ·
      refine ⟨12482925181990865050335563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8321950121327243366890375 12482925181990865050335563)
      ·
        refine ⟨18724387772986297575503345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12482925181990865050335563 18724387772986297575503345)
        ·
          refine ⟨14043290829739723181627509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18724387772986297575503345 14043290829739723181627509)
          ·
            refine ⟨1316558515288099048277579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14043290829739723181627509 1316558515288099048277579)
            ·
              refine ⟨1974837772932148572416369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316558515288099048277579 1974837772932148572416369)
              ·
                refine ⟨1481128329699111429312277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1974837772932148572416369 1481128329699111429312277)
                ·
                  refine ⟨69427890454645848249013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1481128329699111429312277 69427890454645848249013)
                  ·
                    rfl

theorem cell23_1216893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_1216893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216893 prefixEnd_1216893 := by exact prefixLift 1216893
  have htrace : WordTrace (prefixWord ++ tailWord_1216893) baseStart_1216893 baseEnd_1216893 := by
    simpa [prefixWord, tailWord_1216893, baseEnd_1216893] using wordTrace_append hprefix tailTrace_1216893
  have hstable : (prefixWord ++ tailWord_1216893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216893).length < 2 ^ (prefixWord ++ tailWord_1216893).sum := by decide
  have hdescent : baseEnd_1216893 < baseStart_1216893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216910 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_1216910 : Nat := 118140960795 + 1216910 * 2 ^ 59
def prefixEnd_1216910 : Nat := 4983230072969 + 3 ^ 40 * 1216910 * 2
def baseEnd_1216910 : Nat := 69428860362548785303171

theorem tailTrace_1216910 : CollatzResearch.WordTrace tailWord_1216910 prefixEnd_1216910 69428860362548785303171 := by
  unfold tailWord_1216910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548044252668797065848023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29589569347566917684522789 5548044252668797065848023)
  ·
    refine ⟨8322066379003195598772035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5548044252668797065848023 8322066379003195598772035)
    ·
      refine ⟨12483099568504793398158053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8322066379003195598772035 12483099568504793398158053)
      ·
        refine ⟨2340581169094648762154635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12483099568504793398158053 2340581169094648762154635)
        ·
          refine ⟨3510871753641973143231953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340581169094648762154635 3510871753641973143231953)
          ·
            refine ⟨2633153815231479857423965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3510871753641973143231953 2633153815231479857423965)
            ·
              refine ⟨987432680711804946533987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2633153815231479857423965 987432680711804946533987)
              ·
                refine ⟨1481149021067707419800981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987432680711804946533987 1481149021067707419800981)
                ·
                  refine ⟨69428860362548785303171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1481149021067707419800981 69428860362548785303171)
                  ·
                    rfl

theorem cell23_1216910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_1216910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216910 prefixEnd_1216910 := by exact prefixLift 1216910
  have htrace : WordTrace (prefixWord ++ tailWord_1216910) baseStart_1216910 baseEnd_1216910 := by
    simpa [prefixWord, tailWord_1216910, baseEnd_1216910] using wordTrace_append hprefix tailTrace_1216910
  have hstable : (prefixWord ++ tailWord_1216910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216910).length < 2 ^ (prefixWord ++ tailWord_1216910).sum := by decide
  have hdescent : baseEnd_1216910 < baseStart_1216910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216920 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1216920 : Nat := 118140960795 + 1216920 * 2 ^ 59
def prefixEnd_1216920 : Nat := 4983230072969 + 3 ^ 40 * 1216920 * 2
def baseEnd_1216920 : Nat := 624864878069484028603493

theorem tailTrace_1216920 : CollatzResearch.WordTrace tailWord_1216920 prefixEnd_1216920 624864878069484028603493 := by
  unfold tailWord_1216920
  simp only [CollatzResearch.WordTrace]
  refine ⟨22192359375657074117324107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29589812500876098823098809 22192359375657074117324107)
  ·
    refine ⟨33288539063485611175986161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22192359375657074117324107 33288539063485611175986161)
    ·
      refine ⟨24966404297614208381989621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33288539063485611175986161 24966404297614208381989621)
      ·
        refine ⟨2340600402901332035811527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24966404297614208381989621 2340600402901332035811527)
        ·
          refine ⟨3510900604351998053717291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340600402901332035811527 3510900604351998053717291)
          ·
            refine ⟨5266350906527997080575937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510900604351998053717291 5266350906527997080575937)
            ·
              refine ⟨3949763179895997810431953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5266350906527997080575937 3949763179895997810431953)
              ·
                refine ⟨2962322384921998357823965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3949763179895997810431953 2962322384921998357823965)
                ·
                  refine ⟨1110870894345749384183987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2962322384921998357823965 1110870894345749384183987)
                  ·
                    refine ⟨1666306341518624076275981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1110870894345749384183987 1666306341518624076275981)
                    ·
                      refine ⟨624864878069484028603493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1666306341518624076275981 624864878069484028603493)
                      ·
                        rfl

theorem cell23_1216920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1216920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216920 prefixEnd_1216920 := by exact prefixLift 1216920
  have htrace : WordTrace (prefixWord ++ tailWord_1216920) baseStart_1216920 baseEnd_1216920 := by
    simpa [prefixWord, tailWord_1216920, baseEnd_1216920] using wordTrace_append hprefix tailTrace_1216920
  have hstable : (prefixWord ++ tailWord_1216920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216920).length < 2 ^ (prefixWord ++ tailWord_1216920).sum := by decide
  have hdescent : baseEnd_1216920 < baseStart_1216920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216930 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_1216930 : Nat := 118140960795 + 1216930 * 2 ^ 59
def prefixEnd_1216930 : Nat := 4983230072969 + 3 ^ 40 * 1216930 * 2
def baseEnd_1216930 : Nat := 624870012876028989478447

theorem tailTrace_1216930 : CollatzResearch.WordTrace tailWord_1216930 prefixEnd_1216930 624870012876028989478447 := by
  unfold tailWord_1216930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11096270870319479985628061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29590055654185279961674829 11096270870319479985628061)
  ·
    refine ⟨4161101576369804994610523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11096270870319479985628061 4161101576369804994610523)
    ·
      refine ⟨6241652364554707491915785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4161101576369804994610523 6241652364554707491915785)
      ·
        refine ⟨4681239273416030618936839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6241652364554707491915785 4681239273416030618936839)
        ·
          refine ⟨7021858910124045928405259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681239273416030618936839 7021858910124045928405259)
          ·
            refine ⟨10532788365186068892607889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7021858910124045928405259 10532788365186068892607889)
            ·
              refine ⟨7899591273889551669455917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10532788365186068892607889 7899591273889551669455917)
              ·
                refine ⟨2962346727708581876045969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7899591273889551669455917 2962346727708581876045969)
                ·
                  refine ⟨2221760045781436407034477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2962346727708581876045969 2221760045781436407034477)
                  ·
                    refine ⟨833160017168038652637929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2221760045781436407034477 833160017168038652637929)
                    ·
                      refine ⟨624870012876028989478447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833160017168038652637929 624870012876028989478447)
                      ·
                        rfl

theorem cell23_1216930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_1216930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216930 prefixEnd_1216930 := by exact prefixLift 1216930
  have htrace : WordTrace (prefixWord ++ tailWord_1216930) baseStart_1216930 baseEnd_1216930 := by
    simpa [prefixWord, tailWord_1216930, baseEnd_1216930] using wordTrace_append hprefix tailTrace_1216930
  have hstable : (prefixWord ++ tailWord_1216930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216930).length < 2 ^ (prefixWord ++ tailWord_1216930).sum := by decide
  have hdescent : baseEnd_1216930 < baseStart_1216930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216953 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 4, 4]
def baseStart_1216953 : Nat := 118140960795 + 1216953 * 2 ^ 59
def prefixEnd_1216953 : Nat := 4983230072969 + 3 ^ 40 * 1216953 * 2
def baseEnd_1216953 : Nat := 208293940977027466496947

theorem tailTrace_1216953 : CollatzResearch.WordTrace tailWord_1216953 prefixEnd_1216953 208293940977027466496947 := by
  unfold tailWord_1216953
  simp only [CollatzResearch.WordTrace]
  refine ⟨44385922360194594870599513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29590614906796396580399675 44385922360194594870599513)
  ·
    refine ⟨33289441770145946152949635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44385922360194594870599513 33289441770145946152949635)
    ·
      refine ⟨49934162655218919229424453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33289441770145946152949635 49934162655218919229424453)
      ·
        refine ⟨9362655497853547355517085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49934162655218919229424453 9362655497853547355517085)
        ·
          refine ⟨3510995811695080258318907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9362655497853547355517085 3510995811695080258318907)
          ·
            refine ⟨5266493717542620387478361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510995811695080258318907 5266493717542620387478361)
            ·
              refine ⟨3949870288156965290608771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5266493717542620387478361 3949870288156965290608771)
              ·
                refine ⟨5924805432235447935913157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3949870288156965290608771 5924805432235447935913157)
                ·
                  refine ⟨1110901018544146487983717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5924805432235447935913157 1110901018544146487983717)
                  ·
                    refine ⟨208293940977027466496947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1110901018544146487983717 208293940977027466496947)
                    ·
                      rfl

theorem cell23_1216953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 4].length) (baseStart_1216953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216953 prefixEnd_1216953 := by exact prefixLift 1216953
  have htrace : WordTrace (prefixWord ++ tailWord_1216953) baseStart_1216953 baseEnd_1216953 := by
    simpa [prefixWord, tailWord_1216953, baseEnd_1216953] using wordTrace_append hprefix tailTrace_1216953
  have hstable : (prefixWord ++ tailWord_1216953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216953).length < 2 ^ (prefixWord ++ tailWord_1216953).sum := by decide
  have hdescent : baseEnd_1216953 < baseStart_1216953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216961 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 6]
def baseStart_1216961 : Nat := 118140960795 + 1216961 * 2 ^ 59
def prefixEnd_1216961 : Nat := 4983230072969 + 3 ^ 40 * 1216961 * 2
def baseEnd_1216961 : Nat := 69431770086257596465645

theorem tailTrace_1216961 : CollatzResearch.WordTrace tailWord_1216961 prefixEnd_1216961 69431770086257596465645 := by
  unfold tailWord_1216961
  simp only [CollatzResearch.WordTrace]
  refine ⟨44386214144165612236890737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29590809429443741491260491 44386214144165612236890737)
  ·
    refine ⟨33289660608124209177668053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44386214144165612236890737 33289660608124209177668053)
    ·
      refine ⟨780226420502911152601595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33289660608124209177668053 780226420502911152601595)
      ·
        refine ⟨1170339630754366728902393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 780226420502911152601595 1170339630754366728902393)
        ·
          refine ⟨877754723065775046676795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1170339630754366728902393 877754723065775046676795)
          ·
            refine ⟨1316632084598662570015193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877754723065775046676795 1316632084598662570015193)
            ·
              refine ⟨987474063448996927511395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1316632084598662570015193 987474063448996927511395)
              ·
                refine ⟨1481211095173495391267093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987474063448996927511395 1481211095173495391267093)
                ·
                  refine ⟨69431770086257596465645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1481211095173495391267093 69431770086257596465645)
                  ·
                    rfl

theorem cell23_1216961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 6].length) (baseStart_1216961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216961 prefixEnd_1216961 := by exact prefixLift 1216961
  have htrace : WordTrace (prefixWord ++ tailWord_1216961) baseStart_1216961 baseEnd_1216961 := by
    simpa [prefixWord, tailWord_1216961, baseEnd_1216961] using wordTrace_append hprefix tailTrace_1216961
  have hstable : (prefixWord ++ tailWord_1216961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216961).length < 2 ^ (prefixWord ++ tailWord_1216961).sum := by decide
  have hdescent : baseEnd_1216961 < baseStart_1216961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216980 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1216980 : Nat := 118140960795 + 1216980 * 2 ^ 59
def prefixEnd_1216980 : Nat := 4983230072969 + 3 ^ 40 * 1216980 * 2
def baseEnd_1216980 : Nat := 624895686908753793853217

theorem tailTrace_1216980 : CollatzResearch.WordTrace tailWord_1216980 prefixEnd_1216980 624895686908753793853217 := by
  unfold tailWord_1216980
  simp only [CollatzResearch.WordTrace]
  refine ⟨22193453565548389240916197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29591271420731185654554929 22193453565548389240916197)
  ·
    refine ⟨4161272543540322982671787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22193453565548389240916197 4161272543540322982671787)
    ·
      refine ⟨6241908815310484474007681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4161272543540322982671787 6241908815310484474007681)
      ·
        refine ⟨4681431611482863355505761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6241908815310484474007681 4681431611482863355505761)
        ·
          refine ⟨3511073708612147516629321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4681431611482863355505761 3511073708612147516629321)
          ·
            refine ⟨2633305281459110637471991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3511073708612147516629321 2633305281459110637471991)
            ·
              refine ⟨3949957922188665956207987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633305281459110637471991 3949957922188665956207987)
              ·
                refine ⟨5924936883282998934311981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3949957922188665956207987 5924936883282998934311981)
                ·
                  refine ⟨2221851331231124600366993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5924936883282998934311981 2221851331231124600366993)
                  ·
                    refine ⟨1666388498423343450275245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2221851331231124600366993 1666388498423343450275245)
                    ·
                      refine ⟨624895686908753793853217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1666388498423343450275245 624895686908753793853217)
                      ·
                        rfl

theorem cell23_1216980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1216980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216980 prefixEnd_1216980 := by exact prefixLift 1216980
  have htrace : WordTrace (prefixWord ++ tailWord_1216980) baseStart_1216980 baseEnd_1216980 := by
    simpa [prefixWord, tailWord_1216980, baseEnd_1216980] using wordTrace_append hprefix tailTrace_1216980
  have hstable : (prefixWord ++ tailWord_1216980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216980).length < 2 ^ (prefixWord ++ tailWord_1216980).sum := by decide
  have hdescent : baseEnd_1216980 < baseStart_1216980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216993 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_1216993 : Nat := 118140960795 + 1216993 * 2 ^ 59
def prefixEnd_1216993 : Nat := 4983230072969 + 3 ^ 40 * 1216993 * 2
def baseEnd_1216993 : Nat := 624902362157262242990657

theorem tailTrace_1216993 : CollatzResearch.WordTrace tailWord_1216993 prefixEnd_1216993 624902362157262242990657 := by
  unfold tailWord_1216993
  simp only [CollatzResearch.WordTrace]
  refine ⟨44387381280049681702055633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29591587520033121134703755 44387381280049681702055633)
  ·
    refine ⟨33290535960037261276541725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44387381280049681702055633 33290535960037261276541725)
    ·
      refine ⟨12483950985013972978703147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33290535960037261276541725 12483950985013972978703147)
      ·
        refine ⟨18725926477520959468054721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12483950985013972978703147 18725926477520959468054721)
        ·
          refine ⟨14044444858140719601041041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18725926477520959468054721 14044444858140719601041041)
          ·
            refine ⟨10533333643605539700780781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14044444858140719601041041 10533333643605539700780781)
            ·
              refine ⟨3950000116352077387792793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10533333643605539700780781 3950000116352077387792793)
              ·
                refine ⟨2962500087264058040844595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950000116352077387792793 2962500087264058040844595)
                ·
                  refine ⟨4443750130896087061266893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962500087264058040844595 4443750130896087061266893)
                  ·
                    refine ⟨1666406299086032647975085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4443750130896087061266893 1666406299086032647975085)
                    ·
                      refine ⟨624902362157262242990657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1666406299086032647975085 624902362157262242990657)
                      ·
                        rfl

theorem cell23_1216993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_1216993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216993 prefixEnd_1216993 := by exact prefixLift 1216993
  have htrace : WordTrace (prefixWord ++ tailWord_1216993) baseStart_1216993 baseEnd_1216993 := by
    simpa [prefixWord, tailWord_1216993, baseEnd_1216993] using wordTrace_append hprefix tailTrace_1216993
  have hstable : (prefixWord ++ tailWord_1216993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216993).length < 2 ^ (prefixWord ++ tailWord_1216993).sum := by decide
  have hdescent : baseEnd_1216993 < baseStart_1216993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216997 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 1, 1, 5]
def baseStart_1216997 : Nat := 118140960795 + 1216997 * 2 ^ 59
def prefixEnd_1216997 : Nat := 4983230072969 + 3 ^ 40 * 1216997 * 2
def baseEnd_1216997 : Nat := 624904416079880227340639

theorem tailTrace_1216997 : CollatzResearch.WordTrace tailWord_1216997 prefixEnd_1216997 624904416079880227340639 := by
  unfold tailWord_1216997
  simp only [CollatzResearch.WordTrace]
  refine ⟨44387527172035190385201245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29591684781356793590134163 44387527172035190385201245)
  ·
    refine ⟨16645322689513196394450467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44387527172035190385201245 16645322689513196394450467)
    ·
      refine ⟨24967984034269794591675701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16645322689513196394450467 24967984034269794591675701)
      ·
        refine ⟨2340748503212793242969597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24967984034269794591675701 2340748503212793242969597)
        ·
          refine ⟨877780688704797466113599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2340748503212793242969597 877780688704797466113599)
          ·
            refine ⟨1316671033057196199170399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877780688704797466113599 1316671033057196199170399)
            ·
              refine ⟨1975006549585794298755599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1316671033057196199170399 1975006549585794298755599)
              ·
                refine ⟨2962509824378691448133399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975006549585794298755599 2962509824378691448133399)
                ·
                  refine ⟨4443764736568037172200099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962509824378691448133399 4443764736568037172200099)
                  ·
                    refine ⟨6665647104852055758300149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4443764736568037172200099 6665647104852055758300149)
                    ·
                      refine ⟨624904416079880227340639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6665647104852055758300149 624904416079880227340639)
                      ·
                        rfl

theorem cell23_1216997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_1216997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1216997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1216997 prefixEnd_1216997 := by exact prefixLift 1216997
  have htrace : WordTrace (prefixWord ++ tailWord_1216997) baseStart_1216997 baseEnd_1216997 := by
    simpa [prefixWord, tailWord_1216997, baseEnd_1216997] using wordTrace_append hprefix tailTrace_1216997
  have hstable : (prefixWord ++ tailWord_1216997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216997).length < 2 ^ (prefixWord ++ tailWord_1216997).sum := by decide
  have hdescent : baseEnd_1216997 < baseStart_1216997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217016 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_1217016 : Nat := 118140960795 + 1217016 * 2 ^ 59
def prefixEnd_1217016 : Nat := 4983230072969 + 3 ^ 40 * 1217016 * 2
def baseEnd_1217016 : Nat := 624914172212315653003051

theorem tailTrace_1217016 : CollatzResearch.WordTrace tailWord_1217016 prefixEnd_1217016 624914172212315653003051 := by
  unfold tailWord_1217016
  simp only [CollatzResearch.WordTrace]
  refine ⟨22194110079483178315071451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29592146772644237753428601 22194110079483178315071451)
  ·
    refine ⟨33291165119224767472607177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22194110079483178315071451 33291165119224767472607177)
    ·
      refine ⟨24968373839418575604455383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33291165119224767472607177 24968373839418575604455383)
      ·
        refine ⟨37452560759127863406683075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24968373839418575604455383 37452560759127863406683075)
        ·
          refine ⟨56178841138691795110024613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37452560759127863406683075 56178841138691795110024613)
          ·
            refine ⟨10533532713504711583129615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56178841138691795110024613 10533532713504711583129615)
            ·
              refine ⟨15800299070257067374694423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10533532713504711583129615 15800299070257067374694423)
              ·
                refine ⟨23700448605385601062041635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15800299070257067374694423 23700448605385601062041635)
                ·
                  refine ⟨35550672908078401593062453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23700448605385601062041635 35550672908078401593062453)
                  ·
                    refine ⟨3332875585132350149349605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35550672908078401593062453 3332875585132350149349605)
                    ·
                      refine ⟨624914172212315653003051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3332875585132350149349605 624914172212315653003051)
                      ·
                        rfl

theorem cell23_1217016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_1217016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217016 prefixEnd_1217016 := by exact prefixLift 1217016
  have htrace : WordTrace (prefixWord ++ tailWord_1217016) baseStart_1217016 baseEnd_1217016 := by
    simpa [prefixWord, tailWord_1217016, baseEnd_1217016] using wordTrace_append hprefix tailTrace_1217016
  have hstable : (prefixWord ++ tailWord_1217016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217016).length < 2 ^ (prefixWord ++ tailWord_1217016).sum := by decide
  have hdescent : baseEnd_1217016 < baseStart_1217016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217050 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2]
def baseStart_1217050 : Nat := 118140960795 + 1217050 * 2 ^ 59
def prefixEnd_1217050 : Nat := 4983230072969 + 3 ^ 40 * 1217050 * 2
def baseEnd_1217050 : Nat := 624931630554568519977895

theorem tailTrace_1217050 : CollatzResearch.WordTrace tailWord_1217050 prefixEnd_1217050 624931630554568519977895 := by
  unfold tailWord_1217050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11097365060210795109220151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29592973493895453624587069 11097365060210795109220151)
  ·
    refine ⟨16646047590316192663830227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11097365060210795109220151 16646047590316192663830227)
    ·
      refine ⟨24969071385474288995745341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16646047590316192663830227 24969071385474288995745341)
      ·
        refine ⟨9363401769552858373404503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24969071385474288995745341 9363401769552858373404503)
        ·
          refine ⟨14045102654329287560106755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9363401769552858373404503 14045102654329287560106755)
          ·
            refine ⟨21067653981493931340160133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14045102654329287560106755 21067653981493931340160133)
            ·
              refine ⟨3950185121530112126280025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21067653981493931340160133 3950185121530112126280025)
              ·
                refine ⟨2962638841147584094710019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950185121530112126280025 2962638841147584094710019)
                ·
                  refine ⟨4443958261721376142065029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962638841147584094710019 4443958261721376142065029)
                  ·
                    refine ⟨833242174072758026637193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4443958261721376142065029 833242174072758026637193)
                    ·
                      refine ⟨624931630554568519977895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833242174072758026637193 624931630554568519977895)
                      ·
                        rfl

theorem cell23_1217050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_1217050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217050 prefixEnd_1217050 := by exact prefixLift 1217050
  have htrace : WordTrace (prefixWord ++ tailWord_1217050) baseStart_1217050 baseEnd_1217050 := by
    simpa [prefixWord, tailWord_1217050, baseEnd_1217050] using wordTrace_append hprefix tailTrace_1217050
  have hstable : (prefixWord ++ tailWord_1217050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217050).length < 2 ^ (prefixWord ++ tailWord_1217050).sum := by decide
  have hdescent : baseEnd_1217050 < baseStart_1217050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217143 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_1217143 : Nat := 118140960795 + 1217143 * 2 ^ 59
def prefixEnd_1217143 : Nat := 4983230072969 + 3 ^ 40 * 1217143 * 2
def baseEnd_1217143 : Nat := 624979384255436656114967

theorem tailTrace_1217143 : CollatzResearch.WordTrace tailWord_1217143 prefixEnd_1217143 624979384255436656114967 := by
  unfold tailWord_1217143
  simp only [CollatzResearch.WordTrace]
  refine ⟨44392852229506257320016083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29595234819670838213344055 44392852229506257320016083)
  ·
    refine ⟨66589278344259385980024125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44392852229506257320016083 66589278344259385980024125)
    ·
      refine ⟨24970979379097269742509047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66589278344259385980024125 24970979379097269742509047)
      ·
        refine ⟨37456469068645904613763571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24970979379097269742509047 37456469068645904613763571)
        ·
          refine ⟨56184703602968856920645357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37456469068645904613763571 56184703602968856920645357)
          ·
            refine ⟨21069263851113321345242009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56184703602968856920645357 21069263851113321345242009)
            ·
              refine ⟨15801947888334991008931507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21069263851113321345242009 15801947888334991008931507)
              ·
                refine ⟨23702921832502486513397261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15801947888334991008931507 23702921832502486513397261)
                ·
                  refine ⟨8888595687188432442523973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23702921832502486513397261 8888595687188432442523973)
                  ·
                    refine ⟨1666611691347831082973245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8888595687188432442523973 1666611691347831082973245)
                    ·
                      refine ⟨624979384255436656114967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1666611691347831082973245 624979384255436656114967)
                      ·
                        rfl

theorem cell23_1217143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_1217143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217143 prefixEnd_1217143 := by exact prefixLift 1217143
  have htrace : WordTrace (prefixWord ++ tailWord_1217143) baseStart_1217143 baseEnd_1217143 := by
    simpa [prefixWord, tailWord_1217143, baseEnd_1217143] using wordTrace_append hprefix tailTrace_1217143
  have hstable : (prefixWord ++ tailWord_1217143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217143).length < 2 ^ (prefixWord ++ tailWord_1217143).sum := by decide
  have hdescent : baseEnd_1217143 < baseStart_1217143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217180 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 6]
def baseStart_1217180 : Nat := 118140960795 + 1217180 * 2 ^ 59
def prefixEnd_1217180 : Nat := 4983230072969 + 3 ^ 40 * 1217180 * 2
def baseEnd_1217180 : Nat := 69444264782183667928033

theorem tailTrace_1217180 : CollatzResearch.WordTrace tailWord_1217180 prefixEnd_1217180 69444264782183667928033 := by
  unfold tailWord_1217180
  simp only [CollatzResearch.WordTrace]
  refine ⟨22197100865186106319556497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29596134486914808426075329 22197100865186106319556497)
  ·
    refine ⟨16647825648889579739667373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22197100865186106319556497 16647825648889579739667373)
    ·
      refine ⟨6242934618333592402375265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16647825648889579739667373 6242934618333592402375265)
      ·
        refine ⟨4682200963750194301781449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6242934618333592402375265 4682200963750194301781449)
        ·
          refine ⟨3511650722812645726336087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4682200963750194301781449 3511650722812645726336087)
          ·
            refine ⟨5267476084218968589504131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3511650722812645726336087 5267476084218968589504131)
            ·
              refine ⟨7901214126328452884256197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5267476084218968589504131 7901214126328452884256197)
              ·
                refine ⟨1481477648686584915798037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7901214126328452884256197 1481477648686584915798037)
                ·
                  refine ⟨69444264782183667928033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1481477648686584915798037 69444264782183667928033)
                  ·
                    rfl

theorem cell23_1217180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_1217180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217180 prefixEnd_1217180 := by exact prefixLift 1217180
  have htrace : WordTrace (prefixWord ++ tailWord_1217180) baseStart_1217180 baseEnd_1217180 := by
    simpa [prefixWord, tailWord_1217180, baseEnd_1217180] using wordTrace_append hprefix tailTrace_1217180
  have hstable : (prefixWord ++ tailWord_1217180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217180).length < 2 ^ (prefixWord ++ tailWord_1217180).sum := by decide
  have hdescent : baseEnd_1217180 < baseStart_1217180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217184 : List Nat := [2, 1, 1, 4, 4, 1, 1, 4, 1, 4]
def baseStart_1217184 : Nat := 118140960795 + 1217184 * 2 ^ 59
def prefixEnd_1217184 : Nat := 4983230072969 + 3 ^ 40 * 1217184 * 2
def baseEnd_1217184 : Nat := 208333478987423665234093

theorem tailTrace_1217184 : CollatzResearch.WordTrace tailWord_1217184 prefixEnd_1217184 208333478987423665234093 := by
  unfold tailWord_1217184
  simp only [CollatzResearch.WordTrace]
  refine ⟨22197173811178860661129303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29596231748238480881505737 22197173811178860661129303)
  ·
    refine ⟨33295760716768290991693955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22197173811178860661129303 33295760716768290991693955)
    ·
      refine ⟨49943641075152436487540933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33295760716768290991693955 49943641075152436487540933)
      ·
        refine ⟨9364432701591081841413925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49943641075152436487540933 9364432701591081841413925)
        ·
          refine ⟨1755831131548327845265111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9364432701591081841413925 1755831131548327845265111)
          ·
            refine ⟨2633746697322491767897667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755831131548327845265111 2633746697322491767897667)
            ·
              refine ⟨3950620045983737651846501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633746697322491767897667 3950620045983737651846501)
              ·
                refine ⟨740741258621950809721219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3950620045983737651846501 740741258621950809721219)
                ·
                  refine ⟨1111111887932926214581829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740741258621950809721219 1111111887932926214581829)
                  ·
                    refine ⟨208333478987423665234093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1111111887932926214581829 208333478987423665234093)
                    ·
                      rfl

theorem cell23_1217184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 4].length) (baseStart_1217184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217184 prefixEnd_1217184 := by exact prefixLift 1217184
  have htrace : WordTrace (prefixWord ++ tailWord_1217184) baseStart_1217184 baseEnd_1217184 := by
    simpa [prefixWord, tailWord_1217184, baseEnd_1217184] using wordTrace_append hprefix tailTrace_1217184
  have hstable : (prefixWord ++ tailWord_1217184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217184).length < 2 ^ (prefixWord ++ tailWord_1217184).sum := by decide
  have hdescent : baseEnd_1217184 < baseStart_1217184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217193 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 3, 5]
def baseStart_1217193 : Nat := 118140960795 + 1217193 * 2 ^ 59
def prefixEnd_1217193 : Nat := 4983230072969 + 3 ^ 40 * 1217193 * 2
def baseEnd_1217193 : Nat := 208335019429387153496579

theorem tailTrace_1217193 : CollatzResearch.WordTrace tailWord_1217193 prefixEnd_1217193 208335019429387153496579 := by
  unfold tailWord_1217193
  simp only [CollatzResearch.WordTrace]
  refine ⟨44394675879325115859336233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29596450586216743906224155 44394675879325115859336233)
  ·
    refine ⟨33296006909493836894502175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44394675879325115859336233 33296006909493836894502175)
    ·
      refine ⟨49944010364240755341753263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33296006909493836894502175 49944010364240755341753263)
      ·
        refine ⟨74916015546361133012629895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49944010364240755341753263 74916015546361133012629895)
        ·
          refine ⟨112374023319541699518944843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74916015546361133012629895 112374023319541699518944843)
          ·
            refine ⟨168561034979312549278417265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112374023319541699518944843 168561034979312549278417265)
            ·
              refine ⟨126420776234484411958812949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168561034979312549278417265 126420776234484411958812949)
              ·
                refine ⟨5925973885991456810569357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126420776234484411958812949 5925973885991456810569357)
                ·
                  refine ⟨2222240207246796303963509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5925973885991456810569357 2222240207246796303963509)
                  ·
                    refine ⟨208335019429387153496579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2222240207246796303963509 208335019429387153496579)
                    ·
                      rfl

theorem cell23_1217193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_1217193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217193 prefixEnd_1217193 := by exact prefixLift 1217193
  have htrace : WordTrace (prefixWord ++ tailWord_1217193) baseStart_1217193 baseEnd_1217193 := by
    simpa [prefixWord, tailWord_1217193, baseEnd_1217193] using wordTrace_append hprefix tailTrace_1217193
  have hstable : (prefixWord ++ tailWord_1217193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217193).length < 2 ^ (prefixWord ++ tailWord_1217193).sum := by decide
  have hdescent : baseEnd_1217193 < baseStart_1217193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217200 : List Nat := [2, 1, 1, 1, 2, 1, 3, 4, 1, 5, 2]
def baseStart_1217200 : Nat := 118140960795 + 1217200 * 2 ^ 59
def prefixEnd_1217200 : Nat := 4983230072969 + 3 ^ 40 * 1217200 * 2
def baseEnd_1217200 : Nat := 625008652652742933102205

theorem tailTrace_1217200 : CollatzResearch.WordTrace tailWord_1217200 prefixEnd_1217200 625008652652742933102205 := by
  unfold tailWord_1217200
  simp only [CollatzResearch.WordTrace]
  refine ⟨22197465595149878027420527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29596620793533170703227369 22197465595149878027420527)
  ·
    refine ⟨33296198392724817041130791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22197465595149878027420527 33296198392724817041130791)
    ·
      refine ⟨49944297589087225561696187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33296198392724817041130791 49944297589087225561696187)
      ·
        refine ⟨74916446383630838342544281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49944297589087225561696187 74916446383630838342544281)
        ·
          refine ⟨56187334787723128756908211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74916446383630838342544281 56187334787723128756908211)
          ·
            refine ⟨84281002181584693135362317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56187334787723128756908211 84281002181584693135362317)
            ·
              refine ⟨31605375818094259925760869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84281002181584693135362317 31605375818094259925760869)
              ·
                refine ⟨5926007965892673736080163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31605375818094259925760869 5926007965892673736080163)
                ·
                  refine ⟨8889011948839010604120245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5926007965892673736080163 8889011948839010604120245)
                  ·
                    refine ⟨833344870203657244136273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8889011948839010604120245 833344870203657244136273)
                    ·
                      refine ⟨625008652652742933102205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833344870203657244136273 625008652652742933102205)
                      ·
                        rfl

theorem cell23_1217200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 1, 5, 2].length) (baseStart_1217200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217200 prefixEnd_1217200 := by exact prefixLift 1217200
  have htrace : WordTrace (prefixWord ++ tailWord_1217200) baseStart_1217200 baseEnd_1217200 := by
    simpa [prefixWord, tailWord_1217200, baseEnd_1217200] using wordTrace_append hprefix tailTrace_1217200
  have hstable : (prefixWord ++ tailWord_1217200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217200).length < 2 ^ (prefixWord ++ tailWord_1217200).sum := by decide
  have hdescent : baseEnd_1217200 < baseStart_1217200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217210 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_1217210 : Nat := 118140960795 + 1217210 * 2 ^ 59
def prefixEnd_1217210 : Nat := 4983230072969 + 3 ^ 40 * 1217210 * 2
def baseEnd_1217210 : Nat := 208337929153095964659053

theorem tailTrace_1217210 : CollatzResearch.WordTrace tailWord_1217210 prefixEnd_1217210 208337929153095964659053 := by
  unfold tailWord_1217210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11098823980065881940676271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29596863946842351841803389 11098823980065881940676271)
  ·
    refine ⟨16648235970098822911014407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11098823980065881940676271 16648235970098822911014407)
    ·
      refine ⟨24972353955148234366521611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16648235970098822911014407 24972353955148234366521611)
      ·
        refine ⟨37458530932722351549782417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24972353955148234366521611 37458530932722351549782417)
        ·
          refine ⟨28093898199541763662336813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37458530932722351549782417 28093898199541763662336813)
          ·
            refine ⟨10535211824828161373376305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28093898199541763662336813 10535211824828161373376305)
            ·
              refine ⟨7901408868621121030032229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10535211824828161373376305 7901408868621121030032229)
              ·
                refine ⟨1481514162866460193131043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7901408868621121030032229 1481514162866460193131043)
                ·
                  refine ⟨2222271244299690289696565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481514162866460193131043 2222271244299690289696565)
                  ·
                    refine ⟨208337929153095964659053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2222271244299690289696565 208337929153095964659053)
                    ·
                      rfl

theorem cell23_1217210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_1217210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217210 prefixEnd_1217210 := by exact prefixLift 1217210
  have htrace : WordTrace (prefixWord ++ tailWord_1217210) baseStart_1217210 baseEnd_1217210 := by
    simpa [prefixWord, tailWord_1217210, baseEnd_1217210] using wordTrace_append hprefix tailTrace_1217210
  have hstable : (prefixWord ++ tailWord_1217210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217210).length < 2 ^ (prefixWord ++ tailWord_1217210).sum := by decide
  have hdescent : baseEnd_1217210 < baseStart_1217210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217223 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 3, 6]
def baseStart_1217223 : Nat := 118140960795 + 1217223 * 2 ^ 59
def prefixEnd_1217223 : Nat := 4983230072969 + 3 ^ 40 * 1217223 * 2
def baseEnd_1217223 : Nat := 208340154235932114371533

theorem tailTrace_1217223 : CollatzResearch.WordTrace tailWord_1217223 prefixEnd_1217223 208340154235932114371533 := by
  unfold tailWord_1217223
  simp only [CollatzResearch.WordTrace]
  refine ⟨44395770069216430982928323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29597180046144287321952215 44395770069216430982928323)
  ·
    refine ⟨66593655103824646474392485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44395770069216430982928323 66593655103824646474392485)
    ·
      refine ⟨12486310331967121213948591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66593655103824646474392485 12486310331967121213948591)
      ·
        refine ⟨18729465497950681820922887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12486310331967121213948591 18729465497950681820922887)
        ·
          refine ⟨28094198246926022731384331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18729465497950681820922887 28094198246926022731384331)
          ·
            refine ⟨42141297370389034097076497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28094198246926022731384331 42141297370389034097076497)
            ·
              refine ⟨31605973027791775572807373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42141297370389034097076497 31605973027791775572807373)
              ·
                refine ⟨11852239885421915839802765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31605973027791775572807373 11852239885421915839802765)
                ·
                  refine ⟨4444589957033218439926037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11852239885421915839802765 4444589957033218439926037)
                  ·
                    refine ⟨208340154235932114371533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4444589957033218439926037 208340154235932114371533)
                    ·
                      rfl

theorem cell23_1217223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_1217223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217223 prefixEnd_1217223 := by exact prefixLift 1217223
  have htrace : WordTrace (prefixWord ++ tailWord_1217223) baseStart_1217223 baseEnd_1217223 := by
    simpa [prefixWord, tailWord_1217223, baseEnd_1217223] using wordTrace_append hprefix tailTrace_1217223
  have hstable : (prefixWord ++ tailWord_1217223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217223).length < 2 ^ (prefixWord ++ tailWord_1217223).sum := by decide
  have hdescent : baseEnd_1217223 < baseStart_1217223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217224 : List Nat := [2, 1, 3, 1, 2, 3, 1, 5, 1, 1, 3]
def baseStart_1217224 : Nat := 118140960795 + 1217224 * 2 ^ 59
def prefixEnd_1217224 : Nat := 4983230072969 + 3 ^ 40 * 1217224 * 2
def baseEnd_1217224 : Nat := 625020976188450839202095

theorem tailTrace_1217224 : CollatzResearch.WordTrace tailWord_1217224 prefixEnd_1217224 625020976188450839202095 := by
  unfold tailWord_1217224
  simp only [CollatzResearch.WordTrace]
  refine ⟨22197903271106404076857363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29597204361475205435809817 22197903271106404076857363)
  ·
    refine ⟨33296854906659606115286045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22197903271106404076857363 33296854906659606115286045)
    ·
      refine ⟨12486320589997352293232267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33296854906659606115286045 12486320589997352293232267)
      ·
        refine ⟨18729480884996028439848401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12486320589997352293232267 18729480884996028439848401)
        ·
          refine ⟨14047110663747021329886301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18729480884996028439848401 14047110663747021329886301)
          ·
            refine ⟨5267666498905132998707363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14047110663747021329886301 5267666498905132998707363)
            ·
              refine ⟨7901499748357699498061045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5267666498905132998707363 7901499748357699498061045)
              ·
                refine ⟨740765601408534327943223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7901499748357699498061045 740765601408534327943223)
                ·
                  refine ⟨1111148402112801491914835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740765601408534327943223 1111148402112801491914835)
                  ·
                    refine ⟨1666722603169202237872253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1111148402112801491914835 1666722603169202237872253)
                    ·
                      refine ⟨625020976188450839202095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1666722603169202237872253 625020976188450839202095)
                      ·
                        rfl

theorem cell23_1217224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_1217224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217224 prefixEnd_1217224 := by exact prefixLift 1217224
  have htrace : WordTrace (prefixWord ++ tailWord_1217224) baseStart_1217224 baseEnd_1217224 := by
    simpa [prefixWord, tailWord_1217224, baseEnd_1217224] using wordTrace_append hprefix tailTrace_1217224
  have hstable : (prefixWord ++ tailWord_1217224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217224).length < 2 ^ (prefixWord ++ tailWord_1217224).sum := by decide
  have hdescent : baseEnd_1217224 < baseStart_1217224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217270 : List Nat := [5, 1, 1, 1, 1, 2, 3, 9]
def baseStart_1217270 : Nat := 118140960795 + 1217270 * 2 ^ 59
def prefixEnd_1217270 : Nat := 4983230072969 + 3 ^ 40 * 1217270 * 2
def baseEnd_1217270 : Nat := 23149799862909542934329

theorem tailTrace_1217270 : CollatzResearch.WordTrace tailWord_1217270 prefixEnd_1217270 23149799862909542934329 := by
  unfold tailWord_1217270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774842768752884875618079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29598322866697438673259509 2774842768752884875618079)
  ·
    refine ⟨4162264153129327313427119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774842768752884875618079 4162264153129327313427119)
    ·
      refine ⟨6243396229693990970140679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4162264153129327313427119 6243396229693990970140679)
      ·
        refine ⟨9365094344540986455211019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6243396229693990970140679 9365094344540986455211019)
        ·
          refine ⟨14047641516811479682816529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9365094344540986455211019 14047641516811479682816529)
          ·
            refine ⟨10535731137608609762112397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14047641516811479682816529 10535731137608609762112397)
            ·
              refine ⟨3950899176603228660792149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10535731137608609762112397 3950899176603228660792149)
              ·
                refine ⟨23149799862909542934329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3950899176603228660792149 23149799862909542934329)
                ·
                  rfl

theorem cell23_1217270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_1217270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217270 prefixEnd_1217270 := by exact prefixLift 1217270
  have htrace : WordTrace (prefixWord ++ tailWord_1217270) baseStart_1217270 baseEnd_1217270 := by
    simpa [prefixWord, tailWord_1217270, baseEnd_1217270] using wordTrace_append hprefix tailTrace_1217270
  have hstable : (prefixWord ++ tailWord_1217270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217270).length < 2 ^ (prefixWord ++ tailWord_1217270).sum := by decide
  have hdescent : baseEnd_1217270 < baseStart_1217270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217273 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1217273 : Nat := 118140960795 + 1217273 * 2 ^ 59
def prefixEnd_1217273 : Nat := 4983230072969 + 3 ^ 40 * 1217273 * 2
def baseEnd_1217273 : Nat := 625046136740521147489369

theorem tailTrace_1217273 : CollatzResearch.WordTrace tailWord_1217273 prefixEnd_1217273 625046136740521147489369 := by
  unfold tailWord_1217273
  simp only [CollatzResearch.WordTrace]
  refine ⟨44397593719035289522248473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29598395812690193014832315 44397593719035289522248473)
  ·
    refine ⟨33298195289276467141686355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44397593719035289522248473 33298195289276467141686355)
    ·
      refine ⟨49947292933914700712529533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33298195289276467141686355 49947292933914700712529533)
      ·
        refine ⟨18730234850218012767198575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49947292933914700712529533 18730234850218012767198575)
        ·
          refine ⟨28095352275327019150797863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18730234850218012767198575 28095352275327019150797863)
          ·
            refine ⟨42143028412990528726196795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28095352275327019150797863 42143028412990528726196795)
            ·
              refine ⟨63214542619485793089295193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42143028412990528726196795 63214542619485793089295193)
              ·
                refine ⟨47410906964614344816971395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63214542619485793089295193 47410906964614344816971395)
                ·
                  refine ⟨71116360446921517225457093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47410906964614344816971395 71116360446921517225457093)
                  ·
                    refine ⟨13334317583797784479773205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71116360446921517225457093 13334317583797784479773205)
                    ·
                      refine ⟨625046136740521147489369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13334317583797784479773205 625046136740521147489369)
                      ·
                        rfl

theorem cell23_1217273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1217273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217273 prefixEnd_1217273 := by exact prefixLift 1217273
  have htrace : WordTrace (prefixWord ++ tailWord_1217273) baseStart_1217273 baseEnd_1217273 := by
    simpa [prefixWord, tailWord_1217273, baseEnd_1217273] using wordTrace_append hprefix tailTrace_1217273
  have hstable : (prefixWord ++ tailWord_1217273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217273).length < 2 ^ (prefixWord ++ tailWord_1217273).sum := by decide
  have hdescent : baseEnd_1217273 < baseStart_1217273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217283 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 1, 9]
def baseStart_1217283 : Nat := 118140960795 + 1217283 * 2 ^ 59
def prefixEnd_1217283 : Nat := 4983230072969 + 3 ^ 40 * 1217283 * 2
def baseEnd_1217283 : Nat := 208350423849022036121441

theorem tailTrace_1217283 : CollatzResearch.WordTrace tailWord_1217283 prefixEnd_1217283 208350423849022036121441 := by
  unfold tailWord_1217283
  simp only [CollatzResearch.WordTrace]
  refine ⟨44397958448999061230112503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29598638965999374153408335 44397958448999061230112503)
  ·
    refine ⟨66596937673498591845168755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44397958448999061230112503 66596937673498591845168755)
    ·
      refine ⟨99895406510247887767753133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66596937673498591845168755 99895406510247887767753133)
      ·
        refine ⟨37460777441342957912907425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99895406510247887767753133 37460777441342957912907425)
        ·
          refine ⟨28095583081007218434680569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37460777441342957912907425 28095583081007218434680569)
          ·
            refine ⟨21071687310755413826010427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28095583081007218434680569 21071687310755413826010427)
            ·
              refine ⟨31607530966133120739015641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21071687310755413826010427 31607530966133120739015641)
              ·
                refine ⟨23705648224599840554261731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31607530966133120739015641 23705648224599840554261731)
                ·
                  refine ⟨35558472336899760831392597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23705648224599840554261731 35558472336899760831392597)
                  ·
                    refine ⟨208350423849022036121441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 35558472336899760831392597 208350423849022036121441)
                    ·
                      rfl

theorem cell23_1217283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 9].length) (baseStart_1217283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217283 prefixEnd_1217283 := by exact prefixLift 1217283
  have htrace : WordTrace (prefixWord ++ tailWord_1217283) baseStart_1217283 baseEnd_1217283 := by
    simpa [prefixWord, tailWord_1217283, baseEnd_1217283] using wordTrace_append hprefix tailTrace_1217283
  have hstable : (prefixWord ++ tailWord_1217283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217283).length < 2 ^ (prefixWord ++ tailWord_1217283).sum := by decide
  have hdescent : baseEnd_1217283 < baseStart_1217283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217297 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 3]
def baseStart_1217297 : Nat := 118140960795 + 1217297 * 2 ^ 59
def prefixEnd_1217297 : Nat := 4983230072969 + 3 ^ 40 * 1217297 * 2
def baseEnd_1217297 : Nat := 625058460276229053589259

theorem tailTrace_1217297 : CollatzResearch.WordTrace tailWord_1217297 prefixEnd_1217297 625058460276229053589259 := by
  unfold tailWord_1217297
  simp only [CollatzResearch.WordTrace]
  refine ⟨44398469070948341621122145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29598979380632227747414763 44398469070948341621122145)
  ·
    refine ⟨33298851803211256215841609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44398469070948341621122145 33298851803211256215841609)
    ·
      refine ⟨24974138852408442161881207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33298851803211256215841609 24974138852408442161881207)
      ·
        refine ⟨37461208278612663242821811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24974138852408442161881207 37461208278612663242821811)
        ·
          refine ⟨56191812417918994864232717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37461208278612663242821811 56191812417918994864232717)
          ·
            refine ⟨21071929656719623074087269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56191812417918994864232717 21071929656719623074087269)
            ·
              refine ⟨3950986810634929326391363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21071929656719623074087269 3950986810634929326391363)
              ·
                refine ⟨5926480215952393989587045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3950986810634929326391363 5926480215952393989587045)
                ·
                  refine ⟨1111215040491073873047571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5926480215952393989587045 1111215040491073873047571)
                  ·
                    refine ⟨1666822560736610809571357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1111215040491073873047571 1666822560736610809571357)
                    ·
                      refine ⟨625058460276229053589259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1666822560736610809571357 625058460276229053589259)
                      ·
                        rfl

theorem cell23_1217297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_1217297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217297 prefixEnd_1217297 := by exact prefixLift 1217297
  have htrace : WordTrace (prefixWord ++ tailWord_1217297) baseStart_1217297 baseEnd_1217297 := by
    simpa [prefixWord, tailWord_1217297, baseEnd_1217297] using wordTrace_append hprefix tailTrace_1217297
  have hstable : (prefixWord ++ tailWord_1217297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217297).length < 2 ^ (prefixWord ++ tailWord_1217297).sum := by decide
  have hdescent : baseEnd_1217297 < baseStart_1217297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217367 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_1217367 : Nat := 118140960795 + 1217367 * 2 ^ 59
def prefixEnd_1217367 : Nat := 4983230072969 + 3 ^ 40 * 1217367 * 2
def baseEnd_1217367 : Nat := 625094403922043779713937

theorem tailTrace_1217367 : CollatzResearch.WordTrace tailWord_1217367 prefixEnd_1217367 625094403922043779713937 := by
  unfold tailWord_1217367
  simp only [CollatzResearch.WordTrace]
  refine ⟨44401022180694743576170355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29600681453796495717446903 44401022180694743576170355)
  ·
    refine ⟨66601533271042115364255533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44401022180694743576170355 66601533271042115364255533)
    ·
      refine ⟨24975574976640793261595825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66601533271042115364255533 24975574976640793261595825)
      ·
        refine ⟨18731681232480594946196869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24975574976640793261595825 18731681232480594946196869)
        ·
          refine ⟨3512190231090111552411913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18731681232480594946196869 3512190231090111552411913)
          ·
            refine ⟨2634142673317583664308935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3512190231090111552411913 2634142673317583664308935)
            ·
              refine ⟨3951214009976375496463403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634142673317583664308935 3951214009976375496463403)
              ·
                refine ⟨5926821014964563244695105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951214009976375496463403 5926821014964563244695105)
                ·
                  refine ⟨4445115761223422433521329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5926821014964563244695105 4445115761223422433521329)
                  ·
                    refine ⟨3333836820917566825140997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4445115761223422433521329 3333836820917566825140997)
                    ·
                      refine ⟨625094403922043779713937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3333836820917566825140997 625094403922043779713937)
                      ·
                        rfl

theorem cell23_1217367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_1217367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217367 prefixEnd_1217367 := by exact prefixLift 1217367
  have htrace : WordTrace (prefixWord ++ tailWord_1217367) baseStart_1217367 baseEnd_1217367 := by
    simpa [prefixWord, tailWord_1217367, baseEnd_1217367] using wordTrace_append hprefix tailTrace_1217367
  have hstable : (prefixWord ++ tailWord_1217367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217367).length < 2 ^ (prefixWord ++ tailWord_1217367).sum := by decide
  have hdescent : baseEnd_1217367 < baseStart_1217367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217400 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_1217400 : Nat := 118140960795 + 1217400 * 2 ^ 59
def prefixEnd_1217400 : Nat := 4983230072969 + 3 ^ 40 * 1217400 * 2
def baseEnd_1217400 : Nat := 625111348783642150601285

theorem tailTrace_1217400 : CollatzResearch.WordTrace tailWord_1217400 prefixEnd_1217400 625111348783642150601285 := by
  unfold tailWord_1217400
  simp only [CollatzResearch.WordTrace]
  refine ⟨22201112894787595106060827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29601483859716793474747769 22201112894787595106060827)
  ·
    refine ⟨33301669342181392659091241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22201112894787595106060827 33301669342181392659091241)
    ·
      refine ⟨24976252006636044494318431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33301669342181392659091241 24976252006636044494318431)
      ·
        refine ⟨37464378009954066741477647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24976252006636044494318431 37464378009954066741477647)
        ·
          refine ⟨56196567014931100112216471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37464378009954066741477647 56196567014931100112216471)
          ·
            refine ⟨84294850522396650168324707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56196567014931100112216471 84294850522396650168324707)
            ·
              refine ⟨126442275783594975252487061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84294850522396650168324707 126442275783594975252487061)
              ·
                refine ⟨5926981677356014464960331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126442275783594975252487061 5926981677356014464960331)
                ·
                  refine ⟨8890472516034021697440497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5926981677356014464960331 8890472516034021697440497)
                  ·
                    refine ⟨6667854387025516273080373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8890472516034021697440497 6667854387025516273080373)
                    ·
                      refine ⟨625111348783642150601285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6667854387025516273080373 625111348783642150601285)
                      ·
                        rfl

theorem cell23_1217400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_1217400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217400 prefixEnd_1217400 := by exact prefixLift 1217400
  have htrace : WordTrace (prefixWord ++ tailWord_1217400) baseStart_1217400 baseEnd_1217400 := by
    simpa [prefixWord, tailWord_1217400, baseEnd_1217400] using wordTrace_append hprefix tailTrace_1217400
  have hstable : (prefixWord ++ tailWord_1217400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217400).length < 2 ^ (prefixWord ++ tailWord_1217400).sum := by decide
  have hdescent : baseEnd_1217400 < baseStart_1217400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217427 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 1, 6, 2]
def baseStart_1217427 : Nat := 118140960795 + 1217427 * 2 ^ 59
def prefixEnd_1217427 : Nat := 4983230072969 + 3 ^ 40 * 1217427 * 2
def baseEnd_1217427 : Nat := 625125212761313544963661

theorem tailTrace_1217427 : CollatzResearch.WordTrace tailWord_1217427 prefixEnd_1217427 625125212761313544963661 := by
  unfold tailWord_1217427
  simp only [CollatzResearch.WordTrace]
  refine ⟨44403210560477373823354535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29602140373651582548903023 44403210560477373823354535)
  ·
    refine ⟨66604815840716060735031803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44403210560477373823354535 66604815840716060735031803)
    ·
      refine ⟨99907223761074091102547705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66604815840716060735031803 99907223761074091102547705)
      ·
        refine ⟨74930417820805568326910779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99907223761074091102547705 74930417820805568326910779)
        ·
          refine ⟨112395626731208352490366169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74930417820805568326910779 112395626731208352490366169)
          ·
            refine ⟨84296720048406264367774627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112395626731208352490366169 84296720048406264367774627)
            ·
              refine ⟨126445080072609396551661941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84296720048406264367774627 126445080072609396551661941)
              ·
                refine ⟨11854226256807130926718307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126445080072609396551661941 11854226256807130926718307)
                ·
                  refine ⟨17781339385210696390077461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11854226256807130926718307 17781339385210696390077461)
                  ·
                    refine ⟨833500283681751393284881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17781339385210696390077461 833500283681751393284881)
                    ·
                      refine ⟨625125212761313544963661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833500283681751393284881 625125212761313544963661)
                      ·
                        rfl

theorem cell23_1217427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 1, 6, 2].length) (baseStart_1217427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217427 prefixEnd_1217427 := by exact prefixLift 1217427
  have htrace : WordTrace (prefixWord ++ tailWord_1217427) baseStart_1217427 baseEnd_1217427 := by
    simpa [prefixWord, tailWord_1217427, baseEnd_1217427] using wordTrace_append hprefix tailTrace_1217427
  have hstable : (prefixWord ++ tailWord_1217427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217427).length < 2 ^ (prefixWord ++ tailWord_1217427).sum := by decide
  have hdescent : baseEnd_1217427 < baseStart_1217427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217462 : List Nat := [5, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_1217462 : Nat := 118140960795 + 1217462 * 2 ^ 59
def prefixEnd_1217462 : Nat := 4983230072969 + 3 ^ 40 * 1217462 * 2
def baseEnd_1217462 : Nat := 69460353842691212002889

theorem tailTrace_1217462 : CollatzResearch.WordTrace tailWord_1217462 prefixEnd_1217462 69460353842691212002889 := by
  unfold tailWord_1217462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2775280444709410925054915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29602991410233716533919093 2775280444709410925054915)
  ·
    refine ⟨4162920667064116387582373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2775280444709410925054915 4162920667064116387582373)
    ·
      refine ⟨780547625074521822671695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4162920667064116387582373 780547625074521822671695)
      ·
        refine ⟨1170821437611782734007543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 780547625074521822671695 1170821437611782734007543)
        ·
          refine ⟨1756232156417674101011315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170821437611782734007543 1756232156417674101011315)
          ·
            refine ⟨2634348234626511151516973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756232156417674101011315 2634348234626511151516973)
            ·
              refine ⟨987880587984941681818865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2634348234626511151516973 987880587984941681818865)
              ·
                refine ⟨740910440988706261364149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987880587984941681818865 740910440988706261364149)
                ·
                  refine ⟨69460353842691212002889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 740910440988706261364149 69460353842691212002889)
                  ·
                    rfl

theorem cell23_1217462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_1217462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217462 prefixEnd_1217462 := by exact prefixLift 1217462
  have htrace : WordTrace (prefixWord ++ tailWord_1217462) baseStart_1217462 baseEnd_1217462 := by
    simpa [prefixWord, tailWord_1217462, baseEnd_1217462] using wordTrace_append hprefix tailTrace_1217462
  have hstable : (prefixWord ++ tailWord_1217462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217462).length < 2 ^ (prefixWord ++ tailWord_1217462).sum := by decide
  have hdescent : baseEnd_1217462 < baseStart_1217462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217464 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_1217464 : Nat := 118140960795 + 1217464 * 2 ^ 59
def prefixEnd_1217464 : Nat := 4983230072969 + 3 ^ 40 * 1217464 * 2
def baseEnd_1217464 : Nat := 625144211545529900200991

theorem tailTrace_1217464 : CollatzResearch.WordTrace tailWord_1217464 prefixEnd_1217464 625144211545529900200991 := by
  unfold tailWord_1217464
  simp only [CollatzResearch.WordTrace]
  refine ⟨22202280030671664571225723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29603040040895552761634297 22202280030671664571225723)
  ·
    refine ⟨33303420046007496856838585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22202280030671664571225723 33303420046007496856838585)
    ·
      refine ⟨24977565034505622642628939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33303420046007496856838585 24977565034505622642628939)
      ·
        refine ⟨37466347551758433963943409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24977565034505622642628939 37466347551758433963943409)
        ·
          refine ⟨28099760663818825472957557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37466347551758433963943409 28099760663818825472957557)
          ·
            refine ⟨2634352562233014888089771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28099760663818825472957557 2634352562233014888089771)
            ·
              refine ⟨3951528843349522332134657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634352562233014888089771 3951528843349522332134657)
              ·
                refine ⟨2963646632512141749100993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3951528843349522332134657 2963646632512141749100993)
                ·
                  refine ⟨2222734974384106311825745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2963646632512141749100993 2222734974384106311825745)
                  ·
                    refine ⟨1667051230788079733869309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2222734974384106311825745 1667051230788079733869309)
                    ·
                      refine ⟨625144211545529900200991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1667051230788079733869309 625144211545529900200991)
                      ·
                        rfl

theorem cell23_1217464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_1217464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217464 prefixEnd_1217464 := by exact prefixLift 1217464
  have htrace : WordTrace (prefixWord ++ tailWord_1217464) baseStart_1217464 baseEnd_1217464 := by
    simpa [prefixWord, tailWord_1217464, baseEnd_1217464] using wordTrace_append hprefix tailTrace_1217464
  have hstable : (prefixWord ++ tailWord_1217464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217464).length < 2 ^ (prefixWord ++ tailWord_1217464).sum := by decide
  have hdescent : baseEnd_1217464 < baseStart_1217464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217521 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 2, 3, 2]
def baseStart_1217521 : Nat := 118140960795 + 1217521 * 2 ^ 59
def prefixEnd_1217521 : Nat := 4983230072969 + 3 ^ 40 * 1217521 * 2
def baseEnd_1217521 : Nat := 625173479942836177188229

theorem tailTrace_1217521 : CollatzResearch.WordTrace tailWord_1217521 prefixEnd_1217521 625173479942836177188229 := by
  unfold tailWord_1217521
  simp only [CollatzResearch.WordTrace]
  refine ⟨44406639022136827877276417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29604426014757885251517611 44406639022136827877276417)
  ·
    refine ⟨33304979266602620907957313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44406639022136827877276417 33304979266602620907957313)
    ·
      refine ⟨24978734449951965680967985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33304979266602620907957313 24978734449951965680967985)
      ·
        refine ⟨18734050837463974260725989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24978734449951965680967985 18734050837463974260725989)
        ·
          refine ⟨3512634532024495173886123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18734050837463974260725989 3512634532024495173886123)
          ·
            refine ⟨5268951798036742760829185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512634532024495173886123 5268951798036742760829185)
            ·
              refine ⟨3951713848527557070621889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5268951798036742760829185 3951713848527557070621889)
              ·
                refine ⟨2963785386395667802966417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3951713848527557070621889 2963785386395667802966417)
                ·
                  refine ⟨2222839039796750852224813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2963785386395667802966417 2222839039796750852224813)
                  ·
                    refine ⟨833564639923781569584305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2222839039796750852224813 833564639923781569584305)
                    ·
                      refine ⟨625173479942836177188229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833564639923781569584305 625173479942836177188229)
                      ·
                        rfl

theorem cell23_1217521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_1217521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217521 prefixEnd_1217521 := by exact prefixLift 1217521
  have htrace : WordTrace (prefixWord ++ tailWord_1217521) baseStart_1217521 baseEnd_1217521 := by
    simpa [prefixWord, tailWord_1217521, baseEnd_1217521] using wordTrace_append hprefix tailTrace_1217521
  have hstable : (prefixWord ++ tailWord_1217521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217521).length < 2 ^ (prefixWord ++ tailWord_1217521).sum := by decide
  have hdescent : baseEnd_1217521 < baseStart_1217521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217522 : List Nat := [3, 2, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_1217522 : Nat := 118140960795 + 1217522 * 2 ^ 59
def prefixEnd_1217522 : Nat := 4983230072969 + 3 ^ 40 * 1217522 * 2
def baseEnd_1217522 : Nat := 208391331141163557758575

theorem tailTrace_1217522 : CollatzResearch.WordTrace tailWord_1217522 prefixEnd_1217522 208391331141163557758575 := by
  unfold tailWord_1217522
  simp only [CollatzResearch.WordTrace]
  refine ⟨11101668873783301262015705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29604450330088803365375213 11101668873783301262015705)
  ·
    refine ⟨8326251655337475946511779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11101668873783301262015705 8326251655337475946511779)
    ·
      refine ⟨12489377483006213919767669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8326251655337475946511779 12489377483006213919767669)
      ·
        refine ⟨1170879139031832554978219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12489377483006213919767669 1170879139031832554978219)
        ·
          refine ⟨1756318708547748832467329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170879139031832554978219 1756318708547748832467329)
          ·
            refine ⟨1317239031410811624350497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756318708547748832467329 1317239031410811624350497)
            ·
              refine ⟨987929273558108718262873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317239031410811624350497 987929273558108718262873)
              ·
                refine ⟨740946955168581538697155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987929273558108718262873 740946955168581538697155)
                ·
                  refine ⟨1111420432752872308045733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 740946955168581538697155 1111420432752872308045733)
                  ·
                    refine ⟨208391331141163557758575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1111420432752872308045733 208391331141163557758575)
                    ·
                      rfl

theorem cell23_1217522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_1217522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217522 prefixEnd_1217522 := by exact prefixLift 1217522
  have htrace : WordTrace (prefixWord ++ tailWord_1217522) baseStart_1217522 baseEnd_1217522 := by
    simpa [prefixWord, tailWord_1217522, baseEnd_1217522] using wordTrace_append hprefix tailTrace_1217522
  have hstable : (prefixWord ++ tailWord_1217522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217522).length < 2 ^ (prefixWord ++ tailWord_1217522).sum := by decide
  have hdescent : baseEnd_1217522 < baseStart_1217522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217544 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 1, 6]
def baseStart_1217544 : Nat := 118140960795 + 1217544 * 2 ^ 59
def prefixEnd_1217544 : Nat := 4983230072969 + 3 ^ 40 * 1217544 * 2
def baseEnd_1217544 : Nat := 208395096665963195733541

theorem tailTrace_1217544 : CollatzResearch.WordTrace tailWord_1217544 prefixEnd_1217544 208395096665963195733541 := by
  unfold tailWord_1217544
  simp only [CollatzResearch.WordTrace]
  refine ⟨22203738950526751402681843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29604985267369001870242457 22203738950526751402681843)
  ·
    refine ⟨33305608425790127104022765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22203738950526751402681843 33305608425790127104022765)
    ·
      refine ⟨12489603159671297664008537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33305608425790127104022765 12489603159671297664008537)
      ·
        refine ⟨9367202369753473248006403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12489603159671297664008537 9367202369753473248006403)
        ·
          refine ⟨14050803554630209872009605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9367202369753473248006403 14050803554630209872009605)
          ·
            refine ⟨2634525666493164351001801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14050803554630209872009605 2634525666493164351001801)
            ·
              refine ⟨1975894249869873263251351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634525666493164351001801 1975894249869873263251351)
              ·
                refine ⟨2963841374804809894877027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975894249869873263251351 2963841374804809894877027)
                ·
                  refine ⟨4445762062207214842315541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963841374804809894877027 4445762062207214842315541)
                  ·
                    refine ⟨208395096665963195733541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4445762062207214842315541 208395096665963195733541)
                    ·
                      rfl

theorem cell23_1217544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_1217544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217544 prefixEnd_1217544 := by exact prefixLift 1217544
  have htrace : WordTrace (prefixWord ++ tailWord_1217544) baseStart_1217544 baseEnd_1217544 := by
    simpa [prefixWord, tailWord_1217544, baseEnd_1217544] using wordTrace_append hprefix tailTrace_1217544
  have hstable : (prefixWord ++ tailWord_1217544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217544).length < 2 ^ (prefixWord ++ tailWord_1217544).sum := by decide
  have hdescent : baseEnd_1217544 < baseStart_1217544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217565 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 1, 5]
def baseStart_1217565 : Nat := 118140960795 + 1217565 * 2 ^ 59
def prefixEnd_1217565 : Nat := 4983230072969 + 3 ^ 40 * 1217565 * 2
def baseEnd_1217565 : Nat := 208398691030544668346009

theorem tailTrace_1217565 : CollatzResearch.WordTrace tailWord_1217565 prefixEnd_1217565 208398691030544668346009 := by
  unfold tailWord_1217565
  simp only [CollatzResearch.WordTrace]
  refine ⟨44408243833977423391878149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29605495889318282261252099 44408243833977423391878149)
  ·
    refine ⟨8326545718870766885977153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44408243833977423391878149 8326545718870766885977153)
    ·
      refine ⟨6244909289153075164482865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8326545718870766885977153 6244909289153075164482865)
      ·
        refine ⟨4683681966864806373362149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6244909289153075164482865 4683681966864806373362149)
        ·
          refine ⟨878190368787151195005403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4683681966864806373362149 878190368787151195005403)
          ·
            refine ⟨1317285553180726792508105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878190368787151195005403 1317285553180726792508105)
            ·
              refine ⟨987964164885545094381079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317285553180726792508105 987964164885545094381079)
              ·
                refine ⟨1481946247328317641571619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987964164885545094381079 1481946247328317641571619)
                ·
                  refine ⟨2222919370992476462357429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481946247328317641571619 2222919370992476462357429)
                  ·
                    refine ⟨208398691030544668346009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2222919370992476462357429 208398691030544668346009)
                    ·
                      rfl

theorem cell23_1217565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_1217565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217565 prefixEnd_1217565 := by exact prefixLift 1217565
  have htrace : WordTrace (prefixWord ++ tailWord_1217565) baseStart_1217565 baseEnd_1217565 := by
    simpa [prefixWord, tailWord_1217565, baseEnd_1217565] using wordTrace_append hprefix tailTrace_1217565
  have hstable : (prefixWord ++ tailWord_1217565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217565).length < 2 ^ (prefixWord ++ tailWord_1217565).sum := by decide
  have hdescent : baseEnd_1217565 < baseStart_1217565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217568 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1217568 : Nat := 118140960795 + 1217568 * 2 ^ 59
def prefixEnd_1217568 : Nat := 4983230072969 + 3 ^ 40 * 1217568 * 2
def baseEnd_1217568 : Nat := 625197613533597493300513

theorem tailTrace_1217568 : CollatzResearch.WordTrace tailWord_1217568 prefixEnd_1217568 625197613533597493300513 := by
  unfold tailWord_1217568
  simp only [CollatzResearch.WordTrace]
  refine ⟨22204176626483277452118679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29605568835311036602824905 22204176626483277452118679)
  ·
    refine ⟨33306264939724916178178019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22204176626483277452118679 33306264939724916178178019)
    ·
      refine ⟨49959397409587374267267029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33306264939724916178178019 49959397409587374267267029)
      ·
        refine ⟨1170923376787204084389071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 49959397409587374267267029 1170923376787204084389071)
        ·
          refine ⟨1756385065180806126583607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170923376787204084389071 1756385065180806126583607)
          ·
            refine ⟨2634577597771209189875411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756385065180806126583607 2634577597771209189875411)
            ·
              refine ⟨3951866396656813784813117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634577597771209189875411 3951866396656813784813117)
              ·
                refine ⟨1481949898746305169304919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3951866396656813784813117 1481949898746305169304919)
                ·
                  refine ⟨2222924848119457753957379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481949898746305169304919 2222924848119457753957379)
                  ·
                    refine ⟨3334387272179186630936069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2222924848119457753957379 3334387272179186630936069)
                    ·
                      refine ⟨625197613533597493300513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3334387272179186630936069 625197613533597493300513)
                      ·
                        rfl

theorem cell23_1217568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1217568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217568 prefixEnd_1217568 := by exact prefixLift 1217568
  have htrace : WordTrace (prefixWord ++ tailWord_1217568) baseStart_1217568 baseEnd_1217568 := by
    simpa [prefixWord, tailWord_1217568, baseEnd_1217568] using wordTrace_append hprefix tailTrace_1217568
  have hstable : (prefixWord ++ tailWord_1217568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217568).length < 2 ^ (prefixWord ++ tailWord_1217568).sum := by decide
  have hdescent : baseEnd_1217568 < baseStart_1217568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217571 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 3]
def baseStart_1217571 : Nat := 118140960795 + 1217571 * 2 ^ 59
def prefixEnd_1217571 : Nat := 4983230072969 + 3 ^ 40 * 1217571 * 2
def baseEnd_1217571 : Nat := 625199153975560981562999

theorem tailTrace_1217571 : CollatzResearch.WordTrace tailWord_1217571 prefixEnd_1217571 625199153975560981562999 := by
  unfold tailWord_1217571
  simp only [CollatzResearch.WordTrace]
  refine ⟨44408462671955686416596567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29605641781303790944397711 44408462671955686416596567)
  ·
    refine ⟨66612694007933529624894851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44408462671955686416596567 66612694007933529624894851)
    ·
      refine ⟨99919041011900294437342277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66612694007933529624894851 99919041011900294437342277)
      ·
        refine ⟨18734820189731305207001677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99919041011900294437342277 18734820189731305207001677)
        ·
          refine ⟨7025557571149239452625629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18734820189731305207001677 7025557571149239452625629)
          ·
            refine ⟨2634584089180964794734611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7025557571149239452625629 2634584089180964794734611)
            ·
              refine ⟨3951876133771447192101917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634584089180964794734611 3951876133771447192101917)
              ·
                refine ⟨1481953550164292697038219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3951876133771447192101917 1481953550164292697038219)
                ·
                  refine ⟨2222930325246439045557329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481953550164292697038219 2222930325246439045557329)
                  ·
                    refine ⟨1667197743934829284167997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2222930325246439045557329 1667197743934829284167997)
                    ·
                      refine ⟨625199153975560981562999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1667197743934829284167997 625199153975560981562999)
                      ·
                        rfl

theorem cell23_1217571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_1217571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217571 prefixEnd_1217571 := by exact prefixLift 1217571
  have htrace : WordTrace (prefixWord ++ tailWord_1217571) baseStart_1217571 baseEnd_1217571 := by
    simpa [prefixWord, tailWord_1217571, baseEnd_1217571] using wordTrace_append hprefix tailTrace_1217571
  have hstable : (prefixWord ++ tailWord_1217571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217571).length < 2 ^ (prefixWord ++ tailWord_1217571).sum := by decide
  have hdescent : baseEnd_1217571 < baseStart_1217571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217598 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1217598 : Nat := 118140960795 + 1217598 * 2 ^ 59
def prefixEnd_1217598 : Nat := 4983230072969 + 3 ^ 40 * 1217598 * 2
def baseEnd_1217598 : Nat := 625213017953232375925375

theorem tailTrace_1217598 : CollatzResearch.WordTrace tailWord_1217598 prefixEnd_1217598 625213017953232375925375 := by
  unfold tailWord_1217598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5551180930357233753478681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29606298295238580018552965 5551180930357233753478681)
  ·
    refine ⟨4163385697767925315109011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5551180930357233753478681 4163385697767925315109011)
    ·
      refine ⟨6245078546651887972663517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163385697767925315109011 6245078546651887972663517)
      ·
        refine ⟨2341904454994457989748819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6245078546651887972663517 2341904454994457989748819)
        ·
          refine ⟨3512856682491686984623229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2341904454994457989748819 3512856682491686984623229)
          ·
            refine ⟨1317321255934382619233711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3512856682491686984623229 1317321255934382619233711)
            ·
              refine ⟨1975981883901573928850567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317321255934382619233711 1975981883901573928850567)
              ·
                refine ⟨2963972825852360893275851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975981883901573928850567 2963972825852360893275851)
                ·
                  refine ⟨4445959238778541339913777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963972825852360893275851 4445959238778541339913777)
                  ·
                    refine ⟨3334469429083906004935333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4445959238778541339913777 3334469429083906004935333)
                    ·
                      refine ⟨625213017953232375925375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3334469429083906004935333 625213017953232375925375)
                      ·
                        rfl

theorem cell23_1217598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1217598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217598 prefixEnd_1217598 := by exact prefixLift 1217598
  have htrace : WordTrace (prefixWord ++ tailWord_1217598) baseStart_1217598 baseEnd_1217598 := by
    simpa [prefixWord, tailWord_1217598, baseEnd_1217598] using wordTrace_append hprefix tailTrace_1217598
  have hstable : (prefixWord ++ tailWord_1217598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217598).length < 2 ^ (prefixWord ++ tailWord_1217598).sum := by decide
  have hdescent : baseEnd_1217598 < baseStart_1217598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217617 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 1, 8]
def baseStart_1217617 : Nat := 118140960795 + 1217617 * 2 ^ 59
def prefixEnd_1217617 : Nat := 4983230072969 + 3 ^ 40 * 1217617 * 2
def baseEnd_1217617 : Nat := 208407591361889267195929

theorem tailTrace_1217617 : CollatzResearch.WordTrace tailWord_1217617 prefixEnd_1217617 208407591361889267195929 := by
  unfold tailWord_1217617
  simp only [CollatzResearch.WordTrace]
  refine ⟨44410140429789036272771105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29606760286526024181847403 44410140429789036272771105)
  ·
    refine ⟨33307605322341777204578329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44410140429789036272771105 33307605322341777204578329)
    ·
      refine ⟨24980703991756332903433747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33307605322341777204578329 24980703991756332903433747)
      ·
        refine ⟨37471055987634499355150621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24980703991756332903433747 37471055987634499355150621)
        ·
          refine ⟨14051645995362937258181483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37471055987634499355150621 14051645995362937258181483)
          ·
            refine ⟨21077468993044405887272225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14051645995362937258181483 21077468993044405887272225)
            ·
              refine ⟨15808101744783304415454169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21077468993044405887272225 15808101744783304415454169)
              ·
                refine ⟨11856076308587478311590627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15808101744783304415454169 11856076308587478311590627)
                ·
                  refine ⟨17784114462881217467385941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11856076308587478311590627 17784114462881217467385941)
                  ·
                    refine ⟨208407591361889267195929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 17784114462881217467385941 208407591361889267195929)
                    ·
                      rfl

theorem cell23_1217617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_1217617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217617 prefixEnd_1217617 := by exact prefixLift 1217617
  have htrace : WordTrace (prefixWord ++ tailWord_1217617) baseStart_1217617 baseEnd_1217617 := by
    simpa [prefixWord, tailWord_1217617, baseEnd_1217617] using wordTrace_append hprefix tailTrace_1217617
  have hstable : (prefixWord ++ tailWord_1217617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217617).length < 2 ^ (prefixWord ++ tailWord_1217617).sum := by decide
  have hdescent : baseEnd_1217617 < baseStart_1217617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217628 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_1217628 : Nat := 118140960795 + 1217628 * 2 ^ 59
def prefixEnd_1217628 : Nat := 4983230072969 + 3 ^ 40 * 1217628 * 2
def baseEnd_1217628 : Nat := 625228422372867258550237

theorem tailTrace_1217628 : CollatzResearch.WordTrace tailWord_1217628 prefixEnd_1217628 625228422372867258550237 := by
  unfold tailWord_1217628
  simp only [CollatzResearch.WordTrace]
  refine ⟨22205270816374592575710769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29607027755166123434281025 22205270816374592575710769)
  ·
    refine ⟨16653953112280944431783077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22205270816374592575710769 16653953112280944431783077)
    ·
      refine ⟨3122616208552677080959327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16653953112280944431783077 3122616208552677080959327)
      ·
        refine ⟨4683924312829015621438991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3122616208552677080959327 4683924312829015621438991)
        ·
          refine ⟨7025886469243523432158487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4683924312829015621438991 7025886469243523432158487)
          ·
            refine ⟨10538829703865285148237731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7025886469243523432158487 10538829703865285148237731)
            ·
              refine ⟨15808244555797927722356597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10538829703865285148237731 15808244555797927722356597)
              ·
                refine ⟨1482022927106055723970931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15808244555797927722356597 1482022927106055723970931)
                ·
                  refine ⟨2223034390659083585956397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482022927106055723970931 2223034390659083585956397)
                  ·
                    refine ⟨833637896497156344733649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223034390659083585956397 833637896497156344733649)
                    ·
                      refine ⟨625228422372867258550237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833637896497156344733649 625228422372867258550237)
                      ·
                        rfl

theorem cell23_1217628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_1217628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217628 prefixEnd_1217628 := by exact prefixLift 1217628
  have htrace : WordTrace (prefixWord ++ tailWord_1217628) baseStart_1217628 baseEnd_1217628 := by
    simpa [prefixWord, tailWord_1217628, baseEnd_1217628] using wordTrace_append hprefix tailTrace_1217628
  have hstable : (prefixWord ++ tailWord_1217628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217628).length < 2 ^ (prefixWord ++ tailWord_1217628).sum := by decide
  have hdescent : baseEnd_1217628 < baseStart_1217628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217644 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_1217644 : Nat := 118140960795 + 1217644 * 2 ^ 59
def prefixEnd_1217644 : Nat := 4983230072969 + 3 ^ 40 * 1217644 * 2
def baseEnd_1217644 : Nat := 625236638063339195950163

theorem tailTrace_1217644 : CollatzResearch.WordTrace tailWord_1217644 prefixEnd_1217644 625236638063339195950163 := by
  unfold tailWord_1217644
  simp only [CollatzResearch.WordTrace]
  refine ⟨22205562600345609942001993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29607416800460813256002657 22205562600345609942001993)
  ·
    refine ⟨16654171950259207456501495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22205562600345609942001993 16654171950259207456501495)
    ·
      refine ⟨24981257925388811184752243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16654171950259207456501495 24981257925388811184752243)
      ·
        refine ⟨37471886888083216777128365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24981257925388811184752243 37471886888083216777128365)
        ·
          refine ⟨14051957583031206291423137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37471886888083216777128365 14051957583031206291423137)
          ·
            refine ⟨10538968187273404718567353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14051957583031206291423137 10538968187273404718567353)
            ·
              refine ⟨7904226140455053538925515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10538968187273404718567353 7904226140455053538925515)
              ·
                refine ⟨11856339210682580308388273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7904226140455053538925515 11856339210682580308388273)
                ·
                  refine ⟨8892254408011935231291205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11856339210682580308388273 8892254408011935231291205)
                  ·
                    refine ⟨1667297701502237855867101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8892254408011935231291205 1667297701502237855867101)
                    ·
                      refine ⟨625236638063339195950163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1667297701502237855867101 625236638063339195950163)
                      ·
                        rfl

theorem cell23_1217644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_1217644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217644 prefixEnd_1217644 := by exact prefixLift 1217644
  have htrace : WordTrace (prefixWord ++ tailWord_1217644) baseStart_1217644 baseEnd_1217644 := by
    simpa [prefixWord, tailWord_1217644, baseEnd_1217644] using wordTrace_append hprefix tailTrace_1217644
  have hstable : (prefixWord ++ tailWord_1217644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217644).length < 2 ^ (prefixWord ++ tailWord_1217644).sum := by decide
  have hdescent : baseEnd_1217644 < baseStart_1217644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217701 : List Nat := [1, 3, 1, 2, 1, 4, 1, 1, 2, 5, 2]
def baseStart_1217701 : Nat := 118140960795 + 1217701 * 2 ^ 59
def prefixEnd_1217701 : Nat := 4983230072969 + 3 ^ 40 * 1217701 * 2
def baseEnd_1217701 : Nat := 625265906460645472937401

theorem tailTrace_1217701 : CollatzResearch.WordTrace tailWord_1217701 prefixEnd_1217701 625265906460645472937401 := by
  unfold tailWord_1217701
  simp only [CollatzResearch.WordTrace]
  refine ⟨44413204161484718618828957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29608802774323145745885971 44413204161484718618828957)
  ·
    refine ⟨16654951560556769482060859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44413204161484718618828957 16654951560556769482060859)
    ·
      refine ⟨24982427340835154223091289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16654951560556769482060859 24982427340835154223091289)
      ·
        refine ⟨18736820505626365667318467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24982427340835154223091289 18736820505626365667318467)
        ·
          refine ⟨28105230758439548500977701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18736820505626365667318467 28105230758439548500977701)
          ·
            refine ⟨5269730767207415343933319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28105230758439548500977701 5269730767207415343933319)
            ·
              refine ⟨7904596150811123015899979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269730767207415343933319 7904596150811123015899979)
              ·
                refine ⟨11856894226216684523849969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7904596150811123015899979 11856894226216684523849969)
                ·
                  refine ⟨8892670669662513392887477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11856894226216684523849969 8892670669662513392887477)
                  ·
                    refine ⟨833687875280860630583201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8892670669662513392887477 833687875280860630583201)
                    ·
                      refine ⟨625265906460645472937401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833687875280860630583201 625265906460645472937401)
                      ·
                        rfl

theorem cell23_1217701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_1217701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217701 prefixEnd_1217701 := by exact prefixLift 1217701
  have htrace : WordTrace (prefixWord ++ tailWord_1217701) baseStart_1217701 baseEnd_1217701 := by
    simpa [prefixWord, tailWord_1217701, baseEnd_1217701] using wordTrace_append hprefix tailTrace_1217701
  have hstable : (prefixWord ++ tailWord_1217701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217701).length < 2 ^ (prefixWord ++ tailWord_1217701).sum := by decide
  have hdescent : baseEnd_1217701 < baseStart_1217701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217728 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 2, 5]
def baseStart_1217728 : Nat := 118140960795 + 1217728 * 2 ^ 59
def prefixEnd_1217728 : Nat := 4983230072969 + 3 ^ 40 * 1217728 * 2
def baseEnd_1217728 : Nat := 208426590146105622433259

theorem tailTrace_1217728 : CollatzResearch.WordTrace tailWord_1217728 prefixEnd_1217728 208426590146105622433259 := by
  unfold tailWord_1217728
  simp only [CollatzResearch.WordTrace]
  refine ⟨22207094466193451115030919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29609459288257934820041225 22207094466193451115030919)
  ·
    refine ⟨33310641699290176672546379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22207094466193451115030919 33310641699290176672546379)
    ·
      refine ⟨49965962548935265008819569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33310641699290176672546379 49965962548935265008819569)
      ·
        refine ⟨37474471911701448756614677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49965962548935265008819569 37474471911701448756614677)
        ·
          refine ⟨1756615870861005410466313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37474471911701448756614677 1756615870861005410466313)
          ·
            refine ⟨1317461903145754057849735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756615870861005410466313 1317461903145754057849735)
            ·
              refine ⟨1976192854718631086774603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317461903145754057849735 1976192854718631086774603)
              ·
                refine ⟨2964289282077946630161905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976192854718631086774603 2964289282077946630161905)
                ·
                  refine ⟨2223216961558459972621429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2964289282077946630161905 2223216961558459972621429)
                  ·
                    refine ⟨208426590146105622433259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2223216961558459972621429 208426590146105622433259)
                    ·
                      rfl

theorem cell23_1217728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 5].length) (baseStart_1217728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217728 prefixEnd_1217728 := by exact prefixLift 1217728
  have htrace : WordTrace (prefixWord ++ tailWord_1217728) baseStart_1217728 baseEnd_1217728 := by
    simpa [prefixWord, tailWord_1217728, baseEnd_1217728] using wordTrace_append hprefix tailTrace_1217728
  have hstable : (prefixWord ++ tailWord_1217728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217728).length < 2 ^ (prefixWord ++ tailWord_1217728).sum := by decide
  have hdescent : baseEnd_1217728 < baseStart_1217728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217751 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_1217751 : Nat := 118140960795 + 1217751 * 2 ^ 59
def prefixEnd_1217751 : Nat := 4983230072969 + 3 ^ 40 * 1217751 * 2
def baseEnd_1217751 : Nat := 625291580493370277312171

theorem tailTrace_1217751 : CollatzResearch.WordTrace tailWord_1217751 prefixEnd_1217751 625291580493370277312171 := by
  unfold tailWord_1217751
  simp only [CollatzResearch.WordTrace]
  refine ⟨44415027811303577158149107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29610018540869051438766071 44415027811303577158149107)
  ·
    refine ⟨66622541716955365737223661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44415027811303577158149107 66622541716955365737223661)
    ·
      refine ⟨24983453143858262151458873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66622541716955365737223661 24983453143858262151458873)
      ·
        refine ⟨18737589857893696613594155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24983453143858262151458873 18737589857893696613594155)
        ·
          refine ⟨28106384786840544920391233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18737589857893696613594155 28106384786840544920391233)
          ·
            refine ⟨21079788590130408690293425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28106384786840544920391233 21079788590130408690293425)
            ·
              refine ⟨15809841442597806517720069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21079788590130408690293425 15809841442597806517720069)
              ·
                refine ⟨2964345270487088722072513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15809841442597806517720069 2964345270487088722072513)
                ·
                  refine ⟨2223258952865316541554385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2964345270487088722072513 2223258952865316541554385)
                  ·
                    refine ⟨1667444214648987406165789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2223258952865316541554385 1667444214648987406165789)
                    ·
                      refine ⟨625291580493370277312171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1667444214648987406165789 625291580493370277312171)
                      ·
                        rfl

theorem cell23_1217751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_1217751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217751 prefixEnd_1217751 := by exact prefixLift 1217751
  have htrace : WordTrace (prefixWord ++ tailWord_1217751) baseStart_1217751 baseEnd_1217751 := by
    simpa [prefixWord, tailWord_1217751, baseEnd_1217751] using wordTrace_append hprefix tailTrace_1217751
  have hstable : (prefixWord ++ tailWord_1217751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217751).length < 2 ^ (prefixWord ++ tailWord_1217751).sum := by decide
  have hdescent : baseEnd_1217751 < baseStart_1217751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217801 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 1, 5]
def baseStart_1217801 : Nat := 118140960795 + 1217801 * 2 ^ 59
def prefixEnd_1217801 : Nat := 4983230072969 + 3 ^ 40 * 1217801 * 2
def baseEnd_1217801 : Nat := 208439084842031693895647

theorem tailTrace_1217801 : CollatzResearch.WordTrace tailWord_1217801 prefixEnd_1217801 208439084842031693895647 := by
  unfold tailWord_1217801
  simp only [CollatzResearch.WordTrace]
  refine ⟨44416851461122435697469257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29611234307414957131646171 44416851461122435697469257)
  ·
    refine ⟨33312638595841826773101943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44416851461122435697469257 33312638595841826773101943)
    ·
      refine ⟨49968957893762740159652915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33312638595841826773101943 49968957893762740159652915)
      ·
        refine ⟨74953436840644110239479373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49968957893762740159652915 74953436840644110239479373)
        ·
          refine ⟨28107538815241541339804765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74953436840644110239479373 28107538815241541339804765)
          ·
            refine ⟨10540327055715578002426787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28107538815241541339804765 10540327055715578002426787)
            ·
              refine ⟨15810490583573367003640181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10540327055715578002426787 15810490583573367003640181)
              ·
                refine ⟨1482233492210003156591267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15810490583573367003640181 1482233492210003156591267)
                ·
                  refine ⟨2223350238315004734886901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482233492210003156591267 2223350238315004734886901)
                  ·
                    refine ⟨208439084842031693895647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2223350238315004734886901 208439084842031693895647)
                    ·
                      rfl

theorem cell23_1217801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 5].length) (baseStart_1217801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217801 prefixEnd_1217801 := by exact prefixLift 1217801
  have htrace : WordTrace (prefixWord ++ tailWord_1217801) baseStart_1217801 baseEnd_1217801 := by
    simpa [prefixWord, tailWord_1217801, baseEnd_1217801] using wordTrace_append hprefix tailTrace_1217801
  have hstable : (prefixWord ++ tailWord_1217801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217801).length < 2 ^ (prefixWord ++ tailWord_1217801).sum := by decide
  have hdescent : baseEnd_1217801 < baseStart_1217801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217855 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 1, 1, 4]
def baseStart_1217855 : Nat := 118140960795 + 1217855 * 2 ^ 59
def prefixEnd_1217855 : Nat := 4983230072969 + 3 ^ 40 * 1217855 * 2
def baseEnd_1217855 : Nat := 625344982481437870411693

theorem tailTrace_1217855 : CollatzResearch.WordTrace tailWord_1217855 prefixEnd_1217855 625344982481437870411693 := by
  unfold tailWord_1217855
  simp only [CollatzResearch.WordTrace]
  refine ⟨44418821002926802919935019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29612547335284535279956679 44418821002926802919935019)
  ·
    refine ⟨66628231504390204379902529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44418821002926802919935019 66628231504390204379902529)
    ·
      refine ⟨49971173628292653284926897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66628231504390204379902529 49971173628292653284926897)
      ·
        refine ⟨37478380221219489963695173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49971173628292653284926897 37478380221219489963695173)
        ·
          refine ⟨7027196291478654368192845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37478380221219489963695173 7027196291478654368192845)
          ·
            refine ⟨2635198609304495388072317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7027196291478654368192845 2635198609304495388072317)
            ·
              refine ⟨988199478489185770527119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2635198609304495388072317 988199478489185770527119)
              ·
                refine ⟨1482299217733778655790679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988199478489185770527119 1482299217733778655790679)
                ·
                  refine ⟨2223448826600667983686019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482299217733778655790679 2223448826600667983686019)
                  ·
                    refine ⟨3335173239901001975529029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2223448826600667983686019 3335173239901001975529029)
                    ·
                      refine ⟨625344982481437870411693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3335173239901001975529029 625344982481437870411693)
                      ·
                        rfl

theorem cell23_1217855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_1217855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217855 prefixEnd_1217855 := by exact prefixLift 1217855
  have htrace : WordTrace (prefixWord ++ tailWord_1217855) baseStart_1217855 baseEnd_1217855 := by
    simpa [prefixWord, tailWord_1217855, baseEnd_1217855] using wordTrace_append hprefix tailTrace_1217855
  have hstable : (prefixWord ++ tailWord_1217855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217855).length < 2 ^ (prefixWord ++ tailWord_1217855).sum := by decide
  have hdescent : baseEnd_1217855 < baseStart_1217855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217872 : List Nat := [2, 1, 1, 1, 1, 5, 3, 4, 1, 2, 2]
def baseStart_1217872 : Nat := 118140960795 + 1217872 * 2 ^ 59
def prefixEnd_1217872 : Nat := 4983230072969 + 3 ^ 40 * 1217872 * 2
def baseEnd_1217872 : Nat := 625353711652564303899115

theorem tailTrace_1217872 : CollatzResearch.WordTrace tailWord_1217872 prefixEnd_1217872 625353711652564303899115 := by
  unfold tailWord_1217872
  simp only [CollatzResearch.WordTrace]
  refine ⟨22209720521932607411651935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29612960695910143215535913 22209720521932607411651935)
  ·
    refine ⟨33314580782898911117477903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22209720521932607411651935 33314580782898911117477903)
    ·
      refine ⟨49971871174348366676216855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33314580782898911117477903 49971871174348366676216855)
      ·
        refine ⟨74957806761522550014325283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49971871174348366676216855 74957806761522550014325283)
        ·
          refine ⟨112436710142283825021487925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74957806761522550014325283 112436710142283825021487925)
          ·
            refine ⟨10540941575839108595764493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112436710142283825021487925 10540941575839108595764493)
            ·
              refine ⟨3952853090939665723411685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10540941575839108595764493 3952853090939665723411685)
              ·
                refine ⟨741159954551187323139691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3952853090939665723411685 741159954551187323139691)
                ·
                  refine ⟨1111739931826780984709537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741159954551187323139691 1111739931826780984709537)
                  ·
                    refine ⟨833804948870085738532153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1111739931826780984709537 833804948870085738532153)
                    ·
                      refine ⟨625353711652564303899115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833804948870085738532153 625353711652564303899115)
                      ·
                        rfl

theorem cell23_1217872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 4, 1, 2, 2].length) (baseStart_1217872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217872 prefixEnd_1217872 := by exact prefixLift 1217872
  have htrace : WordTrace (prefixWord ++ tailWord_1217872) baseStart_1217872 baseEnd_1217872 := by
    simpa [prefixWord, tailWord_1217872, baseEnd_1217872] using wordTrace_append hprefix tailTrace_1217872
  have hstable : (prefixWord ++ tailWord_1217872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217872).length < 2 ^ (prefixWord ++ tailWord_1217872).sum := by decide
  have hdescent : baseEnd_1217872 < baseStart_1217872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217888 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 3]
def baseStart_1217888 : Nat := 118140960795 + 1217888 * 2 ^ 59
def prefixEnd_1217888 : Nat := 4983230072969 + 3 ^ 40 * 1217888 * 2
def baseEnd_1217888 : Nat := 625361927343036241299041

theorem tailTrace_1217888 : CollatzResearch.WordTrace tailWord_1217888 prefixEnd_1217888 625361927343036241299041 := by
  unfold tailWord_1217888
  simp only [CollatzResearch.WordTrace]
  refine ⟨22210012305903624777943159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29613349741204833037257545 22210012305903624777943159)
  ·
    refine ⟨33315018458855437166914739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22210012305903624777943159 33315018458855437166914739)
    ·
      refine ⟨49972527688283155750372109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33315018458855437166914739 49972527688283155750372109)
      ·
        refine ⟨18739697883106183406389541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49972527688283155750372109 18739697883106183406389541)
        ·
          refine ⟨3513693353082409388698039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18739697883106183406389541 3513693353082409388698039)
          ·
            refine ⟨5270540029623614083047059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3513693353082409388698039 5270540029623614083047059)
            ·
              refine ⟨7905810044435421124570589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270540029623614083047059 7905810044435421124570589)
              ·
                refine ⟨2964678766663282921713971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7905810044435421124570589 2964678766663282921713971)
                ·
                  refine ⟨4447018149994924382570957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964678766663282921713971 4447018149994924382570957)
                  ·
                    refine ⟨1667631806248096643464109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4447018149994924382570957 1667631806248096643464109)
                    ·
                      refine ⟨625361927343036241299041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1667631806248096643464109 625361927343036241299041)
                      ·
                        rfl

theorem cell23_1217888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_1217888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217888 prefixEnd_1217888 := by exact prefixLift 1217888
  have htrace : WordTrace (prefixWord ++ tailWord_1217888) baseStart_1217888 baseEnd_1217888 := by
    simpa [prefixWord, tailWord_1217888, baseEnd_1217888] using wordTrace_append hprefix tailTrace_1217888
  have hstable : (prefixWord ++ tailWord_1217888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217888).length < 2 ^ (prefixWord ++ tailWord_1217888).sum := by decide
  have hdescent : baseEnd_1217888 < baseStart_1217888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217909 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_1217909 : Nat := 118140960795 + 1217909 * 2 ^ 59
def prefixEnd_1217909 : Nat := 4983230072969 + 3 ^ 40 * 1217909 * 2
def baseEnd_1217909 : Nat := 625372710436780659136445

theorem tailTrace_1217909 : CollatzResearch.WordTrace tailWord_1217909 prefixEnd_1217909 625372710436780659136445 := by
  unfold tailWord_1217909
  simp only [CollatzResearch.WordTrace]
  refine ⟨44420790544731170142400781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29613860363154113428267187 44420790544731170142400781)
  ·
    refine ⟨16657796454274188803400293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44420790544731170142400781 16657796454274188803400293)
    ·
      refine ⟨3123336835176410400637555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16657796454274188803400293 3123336835176410400637555)
      ·
        refine ⟨4685005252764615600956333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123336835176410400637555 4685005252764615600956333)
        ·
          refine ⟨1756876969786730850358625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4685005252764615600956333 1756876969786730850358625)
          ·
            refine ⟨1317657727340048137768969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756876969786730850358625 1317657727340048137768969)
            ·
              refine ⟨988243295505036103326727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317657727340048137768969 988243295505036103326727)
              ·
                refine ⟨1482364943257554154990091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988243295505036103326727 1482364943257554154990091)
                ·
                  refine ⟨2223547414886331232485137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482364943257554154990091 2223547414886331232485137)
                  ·
                    refine ⟨1667660561164748424363853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2223547414886331232485137 1667660561164748424363853)
                    ·
                      refine ⟨625372710436780659136445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1667660561164748424363853 625372710436780659136445)
                      ·
                        rfl

theorem cell23_1217909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_1217909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217909 prefixEnd_1217909 := by exact prefixLift 1217909
  have htrace : WordTrace (prefixWord ++ tailWord_1217909) baseStart_1217909 baseEnd_1217909 := by
    simpa [prefixWord, tailWord_1217909, baseEnd_1217909] using wordTrace_append hprefix tailTrace_1217909
  have hstable : (prefixWord ++ tailWord_1217909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217909).length < 2 ^ (prefixWord ++ tailWord_1217909).sum := by decide
  have hdescent : baseEnd_1217909 < baseStart_1217909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217915 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 1, 3, 2]
def baseStart_1217915 : Nat := 118140960795 + 1217915 * 2 ^ 59
def prefixEnd_1217915 : Nat := 4983230072969 + 3 ^ 40 * 1217915 * 2
def baseEnd_1217915 : Nat := 625375791320707635661417

theorem tailTrace_1217915 : CollatzResearch.WordTrace tailWord_1217915 prefixEnd_1217915 625375791320707635661417 := by
  unfold tailWord_1217915
  simp only [CollatzResearch.WordTrace]
  refine ⟨44421009382709433167119199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29614006255139622111412799 44421009382709433167119199)
  ·
    refine ⟨66631514074064149750678799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44421009382709433167119199 66631514074064149750678799)
    ·
      refine ⟨99947271111096224626018199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66631514074064149750678799 99947271111096224626018199)
      ·
        refine ⟨149920906666644336939027299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99947271111096224626018199 149920906666644336939027299)
        ·
          refine ⟨224881359999966505408540949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149920906666644336939027299 224881359999966505408540949)
          ·
            refine ⟨10541313749998429941025357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 224881359999966505408540949 10541313749998429941025357)
            ·
              refine ⟨3952992656249411227884509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10541313749998429941025357 3952992656249411227884509)
              ·
                refine ⟨1482372246093529210456691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3952992656249411227884509 1482372246093529210456691)
                ·
                  refine ⟨2223558369140293815685037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482372246093529210456691 2223558369140293815685037)
                  ·
                    refine ⟨833834388427610180881889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223558369140293815685037 833834388427610180881889)
                    ·
                      refine ⟨625375791320707635661417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833834388427610180881889 625375791320707635661417)
                      ·
                        rfl

theorem cell23_1217915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 3, 2].length) (baseStart_1217915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217915 prefixEnd_1217915 := by exact prefixLift 1217915
  have htrace : WordTrace (prefixWord ++ tailWord_1217915) baseStart_1217915 baseEnd_1217915 := by
    simpa [prefixWord, tailWord_1217915, baseEnd_1217915] using wordTrace_append hprefix tailTrace_1217915
  have hstable : (prefixWord ++ tailWord_1217915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217915).length < 2 ^ (prefixWord ++ tailWord_1217915).sum := by decide
  have hdescent : baseEnd_1217915 < baseStart_1217915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217945 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 1, 4, 2]
def baseStart_1217945 : Nat := 118140960795 + 1217945 * 2 ^ 59
def prefixEnd_1217945 : Nat := 4983230072969 + 3 ^ 40 * 1217945 * 2
def baseEnd_1217945 : Nat := 625391195740342518286279

theorem tailTrace_1217945 : CollatzResearch.WordTrace tailWord_1217945 prefixEnd_1217945 625391195740342518286279 := by
  unfold tailWord_1217945
  simp only [CollatzResearch.WordTrace]
  refine ⟨44422103572600748290711289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29614735715067165527140859 44422103572600748290711289)
  ·
    refine ⟨33316577679450561218033467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44422103572600748290711289 33316577679450561218033467)
    ·
      refine ⟨49974866519175841827050201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33316577679450561218033467 49974866519175841827050201)
      ·
        refine ⟨37481149889381881370287651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49974866519175841827050201 37481149889381881370287651)
        ·
          refine ⟨56221724834072822055431477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37481149889381881370287651 56221724834072822055431477)
          ·
            refine ⟨5270786703194327067696701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56221724834072822055431477 5270786703194327067696701)
            ·
              refine ⟨1976545013697872650386263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5270786703194327067696701 1976545013697872650386263)
              ·
                refine ⟨2964817520546808975579395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976545013697872650386263 2964817520546808975579395)
                ·
                  refine ⟨4447226280820213463369093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964817520546808975579395 4447226280820213463369093)
                  ·
                    refine ⟨833854927653790024381705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4447226280820213463369093 833854927653790024381705)
                    ·
                      refine ⟨625391195740342518286279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833854927653790024381705 625391195740342518286279)
                      ·
                        rfl

theorem cell23_1217945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_1217945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217945 prefixEnd_1217945 := by exact prefixLift 1217945
  have htrace : WordTrace (prefixWord ++ tailWord_1217945) baseStart_1217945 baseEnd_1217945 := by
    simpa [prefixWord, tailWord_1217945, baseEnd_1217945] using wordTrace_append hprefix tailTrace_1217945
  have hstable : (prefixWord ++ tailWord_1217945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217945).length < 2 ^ (prefixWord ++ tailWord_1217945).sum := by decide
  have hdescent : baseEnd_1217945 < baseStart_1217945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217965 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1217965 : Nat := 118140960795 + 1217965 * 2 ^ 59
def prefixEnd_1217965 : Nat := 4983230072969 + 3 ^ 40 * 1217965 * 2
def baseEnd_1217965 : Nat := 625401465353432440036187

theorem tailTrace_1217965 : CollatzResearch.WordTrace tailWord_1217965 prefixEnd_1217965 625401465353432440036187 := by
  unfold tailWord_1217965
  simp only [CollatzResearch.WordTrace]
  refine ⟨44422833032528291706439349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29615222021685527804292899 44422833032528291706439349)
  ·
    refine ⟨4164640596799527347478689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44422833032528291706439349 4164640596799527347478689)
    ·
      refine ⟨3123480447599645510609017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4164640596799527347478689 3123480447599645510609017)
      ·
        refine ⟨2342610335699734132956763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3123480447599645510609017 2342610335699734132956763)
        ·
          refine ⟨3513915503549601199435145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342610335699734132956763 3513915503549601199435145)
          ·
            refine ⟨2635436627662200899576359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3513915503549601199435145 2635436627662200899576359)
            ·
              refine ⟨3953154941493301349364539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635436627662200899576359 3953154941493301349364539)
              ·
                refine ⟨5929732412239952024046809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953154941493301349364539 5929732412239952024046809)
                ·
                  refine ⟨4447299309179964018035107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5929732412239952024046809 4447299309179964018035107)
                  ·
                    refine ⟨6670948963769946027052661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4447299309179964018035107 6670948963769946027052661)
                    ·
                      refine ⟨625401465353432440036187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6670948963769946027052661 625401465353432440036187)
                      ·
                        rfl

theorem cell23_1217965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1217965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217965 prefixEnd_1217965 := by exact prefixLift 1217965
  have htrace : WordTrace (prefixWord ++ tailWord_1217965) baseStart_1217965 baseEnd_1217965 := by
    simpa [prefixWord, tailWord_1217965, baseEnd_1217965] using wordTrace_append hprefix tailTrace_1217965
  have hstable : (prefixWord ++ tailWord_1217965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217965).length < 2 ^ (prefixWord ++ tailWord_1217965).sum := by decide
  have hdescent : baseEnd_1217965 < baseStart_1217965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217968 : List Nat := [2, 1, 1, 1, 2, 1, 1, 9, 5]
def baseStart_1217968 : Nat := 118140960795 + 1217968 * 2 ^ 59
def prefixEnd_1217968 : Nat := 4983230072969 + 3 ^ 40 * 1217968 * 2
def baseEnd_1217968 : Nat := 69489222866155103144297

theorem tailTrace_1217968 : CollatzResearch.WordTrace tailWord_1217968 prefixEnd_1217968 69489222866155103144297 := by
  unfold tailWord_1217968
  simp only [CollatzResearch.WordTrace]
  refine ⟨22211471225758711609399279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29615294967678282145865705 22211471225758711609399279)
  ·
    refine ⟨33317206838638067414098919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22211471225758711609399279 33317206838638067414098919)
    ·
      refine ⟨49975810257957101121148379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33317206838638067414098919 49975810257957101121148379)
      ·
        refine ⟨74963715386935651681722569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49975810257957101121148379 74963715386935651681722569)
        ·
          refine ⟨56222786540201738761291927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74963715386935651681722569 56222786540201738761291927)
          ·
            refine ⟨84334179810302608141937891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56222786540201738761291927 84334179810302608141937891)
            ·
              refine ⟨126501269715453912212906837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84334179810302608141937891 126501269715453912212906837)
              ·
                refine ⟨741218377238987766872501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 126501269715453912212906837 741218377238987766872501)
                ·
                  refine ⟨69489222866155103144297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741218377238987766872501 69489222866155103144297)
                  ·
                    rfl

theorem cell23_1217968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 5].length) (baseStart_1217968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217968 prefixEnd_1217968 := by exact prefixLift 1217968
  have htrace : WordTrace (prefixWord ++ tailWord_1217968) baseStart_1217968 baseEnd_1217968 := by
    simpa [prefixWord, tailWord_1217968, baseEnd_1217968] using wordTrace_append hprefix tailTrace_1217968
  have hstable : (prefixWord ++ tailWord_1217968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217968).length < 2 ^ (prefixWord ++ tailWord_1217968).sum := by decide
  have hdescent : baseEnd_1217968 < baseStart_1217968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217996 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 2, 2, 2]
def baseStart_1217996 : Nat := 118140960795 + 1217996 * 2 ^ 59
def prefixEnd_1217996 : Nat := 4983230072969 + 3 ^ 40 * 1217996 * 2
def baseEnd_1217996 : Nat := 625417383253721818748545

theorem tailTrace_1217996 : CollatzResearch.WordTrace tailWord_1217996 prefixEnd_1217996 625417383253721818748545 := by
  unfold tailWord_1217996
  simp only [CollatzResearch.WordTrace]
  refine ⟨22211981847707992000408921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29615975796943989333878561 22211981847707992000408921)
  ·
    refine ⟨16658986385780994000306691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22211981847707992000408921 16658986385780994000306691)
    ·
      refine ⟨24988479578671491000460037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16658986385780994000306691 24988479578671491000460037)
      ·
        refine ⟨4685339921000904562586257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24988479578671491000460037 4685339921000904562586257)
        ·
          refine ⟨3514004940750678421939693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4685339921000904562586257 3514004940750678421939693)
          ·
            refine ⟨1317751852781504408227385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3514004940750678421939693 1317751852781504408227385)
            ·
              refine ⟨988313889586128306170539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317751852781504408227385 988313889586128306170539)
              ·
                refine ⟨1482470834379192459255809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988313889586128306170539 1482470834379192459255809)
                ·
                  refine ⟨1111853125784394344441857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1482470834379192459255809 1111853125784394344441857)
                  ·
                    refine ⟨833889844338295758331393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1111853125784394344441857 833889844338295758331393)
                    ·
                      refine ⟨625417383253721818748545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 833889844338295758331393 625417383253721818748545)
                      ·
                        rfl

theorem cell23_1217996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_1217996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1217996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1217996 prefixEnd_1217996 := by exact prefixLift 1217996
  have htrace : WordTrace (prefixWord ++ tailWord_1217996) baseStart_1217996 baseEnd_1217996 := by
    simpa [prefixWord, tailWord_1217996, baseEnd_1217996] using wordTrace_append hprefix tailTrace_1217996
  have hstable : (prefixWord ++ tailWord_1217996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217996).length < 2 ^ (prefixWord ++ tailWord_1217996).sum := by decide
  have hdescent : baseEnd_1217996 < baseStart_1217996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218028 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_1218028 : Nat := 118140960795 + 1218028 * 2 ^ 59
def prefixEnd_1218028 : Nat := 4983230072969 + 3 ^ 40 * 1218028 * 2
def baseEnd_1218028 : Nat := 208477938211555231182799

theorem tailTrace_1218028 : CollatzResearch.WordTrace tailWord_1218028 prefixEnd_1218028 208477938211555231182799 := by
  unfold tailWord_1218028
  simp only [CollatzResearch.WordTrace]
  refine ⟨22212565415650026732991369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29616753887533368977321825 22212565415650026732991369)
  ·
    refine ⟨16659424061737520049743527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22212565415650026732991369 16659424061737520049743527)
    ·
      refine ⟨24989136092606280074615291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16659424061737520049743527 24989136092606280074615291)
      ·
        refine ⟨37483704138909420111922937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24989136092606280074615291 37483704138909420111922937)
        ·
          refine ⟨28112778104182065083942203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37483704138909420111922937 28112778104182065083942203)
          ·
            refine ⟨42169167156273097625913305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28112778104182065083942203 42169167156273097625913305)
            ·
              refine ⟨31626875367204823219434979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42169167156273097625913305 31626875367204823219434979)
              ·
                refine ⟨47440313050807234829152469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31626875367204823219434979 47440313050807234829152469)
                ·
                  refine ⟨1111882337128294566308261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47440313050807234829152469 1111882337128294566308261)
                  ·
                    refine ⟨208477938211555231182799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1111882337128294566308261 208477938211555231182799)
                    ·
                      rfl

theorem cell23_1218028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_1218028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218028 prefixEnd_1218028 := by exact prefixLift 1218028
  have htrace : WordTrace (prefixWord ++ tailWord_1218028) baseStart_1218028 baseEnd_1218028 := by
    simpa [prefixWord, tailWord_1218028, baseEnd_1218028] using wordTrace_append hprefix tailTrace_1218028
  have hstable : (prefixWord ++ tailWord_1218028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218028).length < 2 ^ (prefixWord ++ tailWord_1218028).sum := by decide
  have hdescent : baseEnd_1218028 < baseStart_1218028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218062 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 3, 4]
def baseStart_1218062 : Nat := 118140960795 + 1218062 * 2 ^ 59
def prefixEnd_1218062 : Nat := 4983230072969 + 3 ^ 40 * 1218062 * 2
def baseEnd_1218062 : Nat := 208483757658972853507747

theorem tailTrace_1218062 : CollatzResearch.WordTrace tailWord_1218062 prefixEnd_1218062 208483757658972853507747 := by
  unfold tailWord_1218062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553296364147109659090055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29617580608784584848480293 5553296364147109659090055)
  ·
    refine ⟨8329944546220664488635083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5553296364147109659090055 8329944546220664488635083)
    ·
      refine ⟨12494916819330996732952625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8329944546220664488635083 12494916819330996732952625)
      ·
        refine ⟨9371187614498247549714469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12494916819330996732952625 9371187614498247549714469)
        ·
          refine ⟨1757097677718421415571463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9371187614498247549714469 1757097677718421415571463)
          ·
            refine ⟨2635646516577632123357195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757097677718421415571463 2635646516577632123357195)
            ·
              refine ⟨3953469774866448185035793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635646516577632123357195 3953469774866448185035793)
              ·
                refine ⟨2965102331149836138776845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3953469774866448185035793 2965102331149836138776845)
                ·
                  refine ⟨1111913374181188552041317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2965102331149836138776845 1111913374181188552041317)
                  ·
                    refine ⟨208483757658972853507747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1111913374181188552041317 208483757658972853507747)
                    ·
                      rfl

theorem cell23_1218062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_1218062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218062 prefixEnd_1218062 := by exact prefixLift 1218062
  have htrace : WordTrace (prefixWord ++ tailWord_1218062) baseStart_1218062 baseEnd_1218062 := by
    simpa [prefixWord, tailWord_1218062, baseEnd_1218062] using wordTrace_append hprefix tailTrace_1218062
  have hstable : (prefixWord ++ tailWord_1218062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218062).length < 2 ^ (prefixWord ++ tailWord_1218062).sum := by decide
  have hdescent : baseEnd_1218062 < baseStart_1218062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218085 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 3]
def baseStart_1218085 : Nat := 118140960795 + 1218085 * 2 ^ 59
def prefixEnd_1218085 : Nat := 4983230072969 + 3 ^ 40 * 1218085 * 2
def baseEnd_1218085 : Nat := 625463083031971970535635

theorem tailTrace_1218085 : CollatzResearch.WordTrace tailWord_1218085 prefixEnd_1218085 625463083031971970535635 := by
  unfold tailWord_1218085
  simp only [CollatzResearch.WordTrace]
  refine ⟨44427209792093552200807709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29618139861395701467205139 44427209792093552200807709)
  ·
    refine ⟨16660203672035082075302891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44427209792093552200807709 16660203672035082075302891)
    ·
      refine ⟨24990305508052623112954337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16660203672035082075302891 24990305508052623112954337)
      ·
        refine ⟨18742729131039467334715753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24990305508052623112954337 18742729131039467334715753)
        ·
          refine ⟨14057046848279600501036815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18742729131039467334715753 14057046848279600501036815)
          ·
            refine ⟨21085570272419400751555223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14057046848279600501036815 21085570272419400751555223)
            ·
              refine ⟨31628355408629101127332835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21085570272419400751555223 31628355408629101127332835)
              ·
                refine ⟨47442533112943651690999253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31628355408629101127332835 47442533112943651690999253)
                ·
                  refine ⟨1111934369834616836507795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47442533112943651690999253 1111934369834616836507795)
                  ·
                    refine ⟨1667901554751925254761693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1111934369834616836507795 1667901554751925254761693)
                    ·
                      refine ⟨625463083031971970535635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1667901554751925254761693 625463083031971970535635)
                      ·
                        rfl

theorem cell23_1218085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_1218085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218085 prefixEnd_1218085 := by exact prefixLift 1218085
  have htrace : WordTrace (prefixWord ++ tailWord_1218085) baseStart_1218085 baseEnd_1218085 := by
    simpa [prefixWord, tailWord_1218085, baseEnd_1218085] using wordTrace_append hprefix tailTrace_1218085
  have hstable : (prefixWord ++ tailWord_1218085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218085).length < 2 ^ (prefixWord ++ tailWord_1218085).sum := by decide
  have hdescent : baseEnd_1218085 < baseStart_1218085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218128 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_1218128 : Nat := 118140960795 + 1218128 * 2 ^ 59
def prefixEnd_1218128 : Nat := 4983230072969 + 3 ^ 40 * 1218128 * 2
def baseEnd_1218128 : Nat := 625485162700115302297937

theorem tailTrace_1218128 : CollatzResearch.WordTrace tailWord_1218128 prefixEnd_1218128 625485162700115302297937 := by
  unfold tailWord_1218128
  simp only [CollatzResearch.WordTrace]
  refine ⟨22214389065468885272311519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29619185420625180363082025 22214389065468885272311519)
  ·
    refine ⟨33321583598203327908467279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22214389065468885272311519 33321583598203327908467279)
    ·
      refine ⟨49982375397304991862700919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33321583598203327908467279 49982375397304991862700919)
      ·
        refine ⟨74973563095957487794051379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49982375397304991862700919 74973563095957487794051379)
        ·
          refine ⟨112460344643936231691077069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74973563095957487794051379 112460344643936231691077069)
          ·
            refine ⟨42172629241476086884153901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112460344643936231691077069 42172629241476086884153901)
            ·
              refine ⟨15814735965553532581557713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42172629241476086884153901 15814735965553532581557713)
              ·
                refine ⟨11861051974165149436168285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15814735965553532581557713 11861051974165149436168285)
                ·
                  refine ⟨4447894490311931038563107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11861051974165149436168285 4447894490311931038563107)
                  ·
                    refine ⟨6671841735467896557844661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4447894490311931038563107 6671841735467896557844661)
                    ·
                      refine ⟨625485162700115302297937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6671841735467896557844661 625485162700115302297937)
                      ·
                        rfl

theorem cell23_1218128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_1218128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218128 prefixEnd_1218128 := by exact prefixLift 1218128
  have htrace : WordTrace (prefixWord ++ tailWord_1218128) baseStart_1218128 baseEnd_1218128 := by
    simpa [prefixWord, tailWord_1218128, baseEnd_1218128] using wordTrace_append hprefix tailTrace_1218128
  have hstable : (prefixWord ++ tailWord_1218128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218128).length < 2 ^ (prefixWord ++ tailWord_1218128).sum := by decide
  have hdescent : baseEnd_1218128 < baseStart_1218128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218135 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 4, 4]
def baseStart_1218135 : Nat := 118140960795 + 1218135 * 2 ^ 59
def prefixEnd_1218135 : Nat := 4983230072969 + 3 ^ 40 * 1218135 * 2
def baseEnd_1218135 : Nat := 208496252354898924970135

theorem tailTrace_1218135 : CollatzResearch.WordTrace tailWord_1218135 prefixEnd_1218135 208496252354898924970135 := by
  unfold tailWord_1218135
  simp only [CollatzResearch.WordTrace]
  refine ⟨44429033441912410740127859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29619355627941607160085239 44429033441912410740127859)
  ·
    refine ⟨66643550162868616110191789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44429033441912410740127859 66643550162868616110191789)
    ·
      refine ⟨24991331311075731041321921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66643550162868616110191789 24991331311075731041321921)
      ·
        refine ⟨18743498483306798280991441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24991331311075731041321921 18743498483306798280991441)
        ·
          refine ⟨14057623862480098710743581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18743498483306798280991441 14057623862480098710743581)
          ·
            refine ⟨5271608948430037016528843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14057623862480098710743581 5271608948430037016528843)
            ·
              refine ⟨7907413422645055524793265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271608948430037016528843 7907413422645055524793265)
              ·
                refine ⟨5930560066983791643594949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7907413422645055524793265 5930560066983791643594949)
                ·
                  refine ⟨1111980012559460933174053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5930560066983791643594949 1111980012559460933174053)
                  ·
                    refine ⟨208496252354898924970135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1111980012559460933174053 208496252354898924970135)
                    ·
                      rfl

theorem cell23_1218135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_1218135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218135 prefixEnd_1218135 := by exact prefixLift 1218135
  have htrace : WordTrace (prefixWord ++ tailWord_1218135) baseStart_1218135 baseEnd_1218135 := by
    simpa [prefixWord, tailWord_1218135, baseEnd_1218135] using wordTrace_append hprefix tailTrace_1218135
  have hstable : (prefixWord ++ tailWord_1218135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218135).length < 2 ^ (prefixWord ++ tailWord_1218135).sum := by decide
  have hdescent : baseEnd_1218135 < baseStart_1218135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218145 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_1218145 : Nat := 118140960795 + 1218145 * 2 ^ 59
def prefixEnd_1218145 : Nat := 4983230072969 + 3 ^ 40 * 1218145 * 2
def baseEnd_1218145 : Nat := 625493891871241735785359

theorem tailTrace_1218145 : CollatzResearch.WordTrace tailWord_1218145 prefixEnd_1218145 625493891871241735785359 := by
  unfold tailWord_1218145
  simp only [CollatzResearch.WordTrace]
  refine ⟨44429398171876182447991889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29619598781250788298661259 44429398171876182447991889)
  ·
    refine ⟨33322048628907136835993917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44429398171876182447991889 33322048628907136835993917)
    ·
      refine ⟨12495768235840176313497719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33322048628907136835993917 12495768235840176313497719)
      ·
        refine ⟨18743652353760264470246579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12495768235840176313497719 18743652353760264470246579)
        ·
          refine ⟨28115478530640396705369869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18743652353760264470246579 28115478530640396705369869)
          ·
            refine ⟨10543304448990148764513701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28115478530640396705369869 10543304448990148764513701)
            ·
              refine ⟨1976869584185652893346319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10543304448990148764513701 1976869584185652893346319)
              ·
                refine ⟨2965304376278479340019479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976869584185652893346319 2965304376278479340019479)
                ·
                  refine ⟨4447956564417719010029219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965304376278479340019479 4447956564417719010029219)
                  ·
                    refine ⟨6671934846626578515043829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4447956564417719010029219 6671934846626578515043829)
                    ·
                      refine ⟨625493891871241735785359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6671934846626578515043829 625493891871241735785359)
                      ·
                        rfl

theorem cell23_1218145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_1218145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218145 prefixEnd_1218145 := by exact prefixLift 1218145
  have htrace : WordTrace (prefixWord ++ tailWord_1218145) baseStart_1218145 baseEnd_1218145 := by
    simpa [prefixWord, tailWord_1218145, baseEnd_1218145] using wordTrace_append hprefix tailTrace_1218145
  have hstable : (prefixWord ++ tailWord_1218145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218145).length < 2 ^ (prefixWord ++ tailWord_1218145).sum := by decide
  have hdescent : baseEnd_1218145 < baseStart_1218145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218148 : List Nat := [2, 3, 1, 1, 2, 3, 11]
def baseStart_1218148 : Nat := 118140960795 + 1218148 * 2 ^ 59
def prefixEnd_1218148 : Nat := 4983230072969 + 3 ^ 40 * 1218148 * 2
def baseEnd_1218148 : Nat := 7722165831027224988245

theorem tailTrace_1218148 : CollatzResearch.WordTrace tailWord_1218148 prefixEnd_1218148 7722165831027224988245 := by
  unfold tailWord_1218148
  simp only [CollatzResearch.WordTrace]
  refine ⟨22214753795432656980175549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29619671727243542640234065 22214753795432656980175549)
  ·
    refine ⟨8330532673287246367565831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22214753795432656980175549 8330532673287246367565831)
    ·
      refine ⟨12495799009930869551348747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8330532673287246367565831 12495799009930869551348747)
      ·
        refine ⟨18743698514896304327023121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12495799009930869551348747 18743698514896304327023121)
        ·
          refine ⟨14057773886172228245267341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18743698514896304327023121 14057773886172228245267341)
          ·
            refine ⟨5271665207314585591975253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14057773886172228245267341 5271665207314585591975253)
            ·
              refine ⟨7722165831027224988245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5271665207314585591975253 7722165831027224988245)
              ·
                rfl

theorem cell23_1218148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 11].length) (baseStart_1218148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218148 prefixEnd_1218148 := by exact prefixLift 1218148
  have htrace : WordTrace (prefixWord ++ tailWord_1218148) baseStart_1218148 baseEnd_1218148 := by
    simpa [prefixWord, tailWord_1218148, baseEnd_1218148] using wordTrace_append hprefix tailTrace_1218148
  have hstable : (prefixWord ++ tailWord_1218148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218148).length < 2 ^ (prefixWord ++ tailWord_1218148).sum := by decide
  have hdescent : baseEnd_1218148 < baseStart_1218148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218152 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 4, 4]
def baseStart_1218152 : Nat := 118140960795 + 1218152 * 2 ^ 59
def prefixEnd_1218152 : Nat := 4983230072969 + 3 ^ 40 * 1218152 * 2
def baseEnd_1218152 : Nat := 208499162078607736132609

theorem tailTrace_1218152 : CollatzResearch.WordTrace tailWord_1218152 prefixEnd_1218152 208499162078607736132609 := by
  unfold tailWord_1218152
  simp only [CollatzResearch.WordTrace]
  refine ⟨22214826741425411321748355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29619768988567215095664473 22214826741425411321748355)
  ·
    refine ⟨33322240112138116982622533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22214826741425411321748355 33322240112138116982622533)
    ·
      refine ⟨6247920021025896934241725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33322240112138116982622533 6247920021025896934241725)
      ·
        refine ⟨2342970007884711350340647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6247920021025896934241725 2342970007884711350340647)
        ·
          refine ⟨3514455011827067025510971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342970007884711350340647 3514455011827067025510971)
          ·
            refine ⟨5271682517740600538266457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514455011827067025510971 5271682517740600538266457)
            ·
              refine ⟨3953761888305450403699843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5271682517740600538266457 3953761888305450403699843)
              ·
                refine ⟨5930642832458175605549765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953761888305450403699843 5930642832458175605549765)
                ·
                  refine ⟨1111995531085907926040581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5930642832458175605549765 1111995531085907926040581)
                  ·
                    refine ⟨208499162078607736132609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1111995531085907926040581 208499162078607736132609)
                    ·
                      rfl

theorem cell23_1218152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_1218152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218152 prefixEnd_1218152 := by exact prefixLift 1218152
  have htrace : WordTrace (prefixWord ++ tailWord_1218152) baseStart_1218152 baseEnd_1218152 := by
    simpa [prefixWord, tailWord_1218152, baseEnd_1218152] using wordTrace_append hprefix tailTrace_1218152
  have hstable : (prefixWord ++ tailWord_1218152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218152).length < 2 ^ (prefixWord ++ tailWord_1218152).sum := by decide
  have hdescent : baseEnd_1218152 < baseStart_1218152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218165 : List Nat := [1, 3, 4, 2, 1, 1, 1, 10]
def baseStart_1218165 : Nat := 118140960795 + 1218165 * 2 ^ 59
def prefixEnd_1218165 : Nat := 4983230072969 + 3 ^ 40 * 1218165 * 2
def baseEnd_1218165 : Nat := 23166820795715987316121

theorem tailTrace_1218165 : CollatzResearch.WordTrace tailWord_1218165 prefixEnd_1218165 23166820795715987316121 := by
  unfold tailWord_1218165
  simp only [CollatzResearch.WordTrace]
  refine ⟨44430127631803725863719949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29620085087869150575813299 44430127631803725863719949)
  ·
    refine ⟨16661297861926397198894981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44430127631803725863719949 16661297861926397198894981)
    ·
      refine ⟨3123993349111199474792809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16661297861926397198894981 3123993349111199474792809)
      ·
        refine ⟨2342995011833399606094607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3123993349111199474792809 2342995011833399606094607)
        ·
          refine ⟨3514492517750099409141911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342995011833399606094607 3514492517750099409141911)
          ·
            refine ⟨5271738776625149113712867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514492517750099409141911 5271738776625149113712867)
            ·
              refine ⟨7907608164937723670569301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271738776625149113712867 7907608164937723670569301)
              ·
                refine ⟨23166820795715987316121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7907608164937723670569301 23166820795715987316121)
                ·
                  rfl

theorem cell23_1218165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 10].length) (baseStart_1218165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218165 prefixEnd_1218165 := by exact prefixLift 1218165
  have htrace : WordTrace (prefixWord ++ tailWord_1218165) baseStart_1218165 baseEnd_1218165 := by
    simpa [prefixWord, tailWord_1218165, baseEnd_1218165] using wordTrace_append hprefix tailTrace_1218165
  have hstable : (prefixWord ++ tailWord_1218165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218165).length < 2 ^ (prefixWord ++ tailWord_1218165).sum := by decide
  have hdescent : baseEnd_1218165 < baseStart_1218165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218196 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_1218196 : Nat := 118140960795 + 1218196 * 2 ^ 59
def prefixEnd_1218196 : Nat := 4983230072969 + 3 ^ 40 * 1218196 * 2
def baseEnd_1218196 : Nat := 625520079384621036247625

theorem tailTrace_1218196 : CollatzResearch.WordTrace tailWord_1218196 prefixEnd_1218196 625520079384621036247625 := by
  unfold tailWord_1218196
  simp only [CollatzResearch.WordTrace]
  refine ⟨22215629147345709079049221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29620838863127612105398961 22215629147345709079049221)
  ·
    refine ⟨4165430465127320452321729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22215629147345709079049221 4165430465127320452321729)
    ·
      refine ⟨3124072848845490339241297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4165430465127320452321729 3124072848845490339241297)
      ·
        refine ⟨2343054636634117754430973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3124072848845490339241297 2343054636634117754430973)
        ·
          refine ⟨878645488737794157911615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2343054636634117754430973 878645488737794157911615)
          ·
            refine ⟨1317968233106691236867423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878645488737794157911615 1317968233106691236867423)
            ·
              refine ⟨1976952349660036855301135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317968233106691236867423 1976952349660036855301135)
              ·
                refine ⟨2965428524490055282951703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976952349660036855301135 2965428524490055282951703)
                ·
                  refine ⟨4448142786735082924427555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965428524490055282951703 4448142786735082924427555)
                  ·
                    refine ⟨6672214180102624386641333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4448142786735082924427555 6672214180102624386641333)
                    ·
                      refine ⟨625520079384621036247625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6672214180102624386641333 625520079384621036247625)
                      ·
                        rfl

theorem cell23_1218196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_1218196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218196 prefixEnd_1218196 := by exact prefixLift 1218196
  have htrace : WordTrace (prefixWord ++ tailWord_1218196) baseStart_1218196 baseEnd_1218196 := by
    simpa [prefixWord, tailWord_1218196, baseEnd_1218196] using wordTrace_append hprefix tailTrace_1218196
  have hstable : (prefixWord ++ tailWord_1218196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218196).length < 2 ^ (prefixWord ++ tailWord_1218196).sum := by decide
  have hdescent : baseEnd_1218196 < baseStart_1218196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218209 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1218209 : Nat := 118140960795 + 1218209 * 2 ^ 59
def prefixEnd_1218209 : Nat := 4983230072969 + 3 ^ 40 * 1218209 * 2
def baseEnd_1218209 : Nat := 625526754633129485385065

theorem tailTrace_1218209 : CollatzResearch.WordTrace tailWord_1218209 prefixEnd_1218209 625526754633129485385065 := by
  unfold tailWord_1218209
  simp only [CollatzResearch.WordTrace]
  refine ⟨44431732443644321378321681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29621154962429547585547787 44431732443644321378321681)
  ·
    refine ⟨33323799332733241033741261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44431732443644321378321681 33323799332733241033741261)
    ·
      refine ⟨12496424749774965387652973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33323799332733241033741261 12496424749774965387652973)
      ·
        refine ⟨4686159281165612020369865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12496424749774965387652973 4686159281165612020369865)
        ·
          refine ⟨3514619460874209015277399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4686159281165612020369865 3514619460874209015277399)
          ·
            refine ⟨5271929191311313522916099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514619460874209015277399 5271929191311313522916099)
            ·
              refine ⟨7907893786966970284374149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271929191311313522916099 7907893786966970284374149)
              ·
                refine ⟨1482730085056306928320153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7907893786966970284374149 1482730085056306928320153)
                ·
                  refine ⟨1112047563792230196240115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1482730085056306928320153 1112047563792230196240115)
                  ·
                    refine ⟨1668071345688345294360173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1112047563792230196240115 1668071345688345294360173)
                    ·
                      refine ⟨625526754633129485385065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1668071345688345294360173 625526754633129485385065)
                      ·
                        rfl

theorem cell23_1218209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1218209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218209 prefixEnd_1218209 := by exact prefixLift 1218209
  have htrace : WordTrace (prefixWord ++ tailWord_1218209) baseStart_1218209 baseEnd_1218209 := by
    simpa [prefixWord, tailWord_1218209, baseEnd_1218209] using wordTrace_append hprefix tailTrace_1218209
  have hstable : (prefixWord ++ tailWord_1218209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218209).length < 2 ^ (prefixWord ++ tailWord_1218209).sum := by decide
  have hdescent : baseEnd_1218209 < baseStart_1218209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218210 : List Nat := [3, 3, 1, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_1218210 : Nat := 118140960795 + 1218210 * 2 ^ 59
def prefixEnd_1218210 : Nat := 4983230072969 + 3 ^ 40 * 1218210 * 2
def baseEnd_1218210 : Nat := 625527268113783981472561

theorem tailTrace_1218210 : CollatzResearch.WordTrace tailWord_1218210 prefixEnd_1218210 625527268113783981472561 := by
  unfold tailWord_1218210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11107942229160174637277021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29621179277760465699405389 11107942229160174637277021)
  ·
    refine ⟨4165478335935065488978883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11107942229160174637277021 4165478335935065488978883)
    ·
      refine ⟨6248217503902598233468325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4165478335935065488978883 6248217503902598233468325)
      ·
        refine ⟨1171540781981737168775311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6248217503902598233468325 1171540781981737168775311)
        ·
          refine ⟨1757311172972605753162967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171540781981737168775311 1757311172972605753162967)
          ·
            refine ⟨2635966759458908629744451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757311172972605753162967 2635966759458908629744451)
            ·
              refine ⟨3953950139188362944616677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635966759458908629744451 3953950139188362944616677)
              ·
                refine ⟨741365651097818052115627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3953950139188362944616677 741365651097818052115627)
                ·
                  refine ⟨1112048476646727078173441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 741365651097818052115627 1112048476646727078173441)
                  ·
                    refine ⟨834036357485045308630081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1112048476646727078173441 834036357485045308630081)
                    ·
                      refine ⟨625527268113783981472561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834036357485045308630081 625527268113783981472561)
                      ·
                        rfl

theorem cell23_1218210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_1218210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218210 prefixEnd_1218210 := by exact prefixLift 1218210
  have htrace : WordTrace (prefixWord ++ tailWord_1218210) baseStart_1218210 baseEnd_1218210 := by
    simpa [prefixWord, tailWord_1218210, baseEnd_1218210] using wordTrace_append hprefix tailTrace_1218210
  have hstable : (prefixWord ++ tailWord_1218210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218210).length < 2 ^ (prefixWord ++ tailWord_1218210).sum := by decide
  have hdescent : baseEnd_1218210 < baseStart_1218210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218216 : List Nat := [2, 1, 7, 1, 1, 2, 1, 8]
def baseStart_1218216 : Nat := 118140960795 + 1218216 * 2 ^ 59
def prefixEnd_1218216 : Nat := 4983230072969 + 3 ^ 40 * 1218216 * 2
def baseEnd_1218216 : Nat := 23167790703618924370279

theorem tailTrace_1218216 : CollatzResearch.WordTrace tailWord_1218216 prefixEnd_1218216 23167790703618924370279 := by
  unfold tailWord_1218216
  simp only [CollatzResearch.WordTrace]
  refine ⟨22215993877309480786913251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29621325169745974382551001 22215993877309480786913251)
  ·
    refine ⟨33323990815964221180369877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22215993877309480786913251 33323990815964221180369877)
    ·
      refine ⟨781031034749161433914919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 33323990815964221180369877 781031034749161433914919)
      ·
        refine ⟨1171546552123742150872379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781031034749161433914919 1171546552123742150872379)
        ·
          refine ⟨1757319828185613226308569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171546552123742150872379 1757319828185613226308569)
          ·
            refine ⟨1317989871139209919731427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1757319828185613226308569 1317989871139209919731427)
            ·
              refine ⟨1976984806708814879597141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317989871139209919731427 1976984806708814879597141)
              ·
                refine ⟨23167790703618924370279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1976984806708814879597141 23167790703618924370279)
                ·
                  rfl

theorem cell23_1218216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 8].length) (baseStart_1218216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218216 prefixEnd_1218216 := by exact prefixLift 1218216
  have htrace : WordTrace (prefixWord ++ tailWord_1218216) baseStart_1218216 baseEnd_1218216 := by
    simpa [prefixWord, tailWord_1218216, baseEnd_1218216] using wordTrace_append hprefix tailTrace_1218216
  have hstable : (prefixWord ++ tailWord_1218216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218216).length < 2 ^ (prefixWord ++ tailWord_1218216).sum := by decide
  have hdescent : baseEnd_1218216 < baseStart_1218216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218253 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_1218253 : Nat := 118140960795 + 1218253 * 2 ^ 59
def prefixEnd_1218253 : Nat := 4983230072969 + 3 ^ 40 * 1218253 * 2
def baseEnd_1218253 : Nat := 625549347781927313234863

theorem tailTrace_1218253 : CollatzResearch.WordTrace tailWord_1218253 prefixEnd_1218253 625549347781927313234863 := by
  unfold tailWord_1218253
  simp only [CollatzResearch.WordTrace]
  refine ⟨44433337255484916892923413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29622224836989944595282275 44433337255484916892923413)
  ·
    refine ⟨2082812683850855479355785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44433337255484916892923413 2082812683850855479355785)
    ·
      refine ⟨1562109512888141609516839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2082812683850855479355785 1562109512888141609516839)
      ·
        refine ⟨2343164269332212414275259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562109512888141609516839 2343164269332212414275259)
        ·
          refine ⟨3514746403998318621412889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2343164269332212414275259 3514746403998318621412889)
          ·
            refine ⟨2636059802998738966059667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3514746403998318621412889 2636059802998738966059667)
            ·
              refine ⟨3954089704498108449089501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2636059802998738966059667 3954089704498108449089501)
              ·
                refine ⟨1482783639186790668408563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3954089704498108449089501 1482783639186790668408563)
                ·
                  refine ⟨2224175458780186002612845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482783639186790668408563 2224175458780186002612845)
                  ·
                    refine ⟨834065797042569750979817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2224175458780186002612845 834065797042569750979817)
                    ·
                      refine ⟨625549347781927313234863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834065797042569750979817 625549347781927313234863)
                      ·
                        rfl

theorem cell23_1218253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_1218253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218253 prefixEnd_1218253 := by exact prefixLift 1218253
  have htrace : WordTrace (prefixWord ++ tailWord_1218253) baseStart_1218253 baseEnd_1218253 := by
    simpa [prefixWord, tailWord_1218253, baseEnd_1218253] using wordTrace_append hprefix tailTrace_1218253
  have hstable : (prefixWord ++ tailWord_1218253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218253).length < 2 ^ (prefixWord ++ tailWord_1218253).sum := by decide
  have hdescent : baseEnd_1218253 < baseStart_1218253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218266 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2]
def baseStart_1218266 : Nat := 118140960795 + 1218266 * 2 ^ 59
def prefixEnd_1218266 : Nat := 4983230072969 + 3 ^ 40 * 1218266 * 2
def baseEnd_1218266 : Nat := 625556023030435762372303

theorem tailTrace_1218266 : CollatzResearch.WordTrace tailWord_1218266 prefixEnd_1218266 625556023030435762372303 := by
  unfold tailWord_1218266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11108452851109455028286663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29622540936291880075431101 11108452851109455028286663)
  ·
    refine ⟨16662679276664182542429995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11108452851109455028286663 16662679276664182542429995)
    ·
      refine ⟨24994018914996273813644993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16662679276664182542429995 24994018914996273813644993)
      ·
        refine ⟨18745514186247205360233745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24994018914996273813644993 18745514186247205360233745)
        ·
          refine ⟨14059135639685404020175309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18745514186247205360233745 14059135639685404020175309)
          ·
            refine ⟨5272175864882026507565741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14059135639685404020175309 5272175864882026507565741)
            ·
              refine ⟨1977065949330759940337153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5272175864882026507565741 1977065949330759940337153)
              ·
                refine ⟨1482799461998069955252865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1977065949330759940337153 1482799461998069955252865)
                ·
                  refine ⟨1112099596498552466439649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1482799461998069955252865 1112099596498552466439649)
                  ·
                    refine ⟨834074697373914349829737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1112099596498552466439649 834074697373914349829737)
                    ·
                      refine ⟨625556023030435762372303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834074697373914349829737 625556023030435762372303)
                      ·
                        rfl

theorem cell23_1218266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_1218266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218266 prefixEnd_1218266 := by exact prefixLift 1218266
  have htrace : WordTrace (prefixWord ++ tailWord_1218266) baseStart_1218266 baseEnd_1218266 := by
    simpa [prefixWord, tailWord_1218266, baseEnd_1218266] using wordTrace_append hprefix tailTrace_1218266
  have hstable : (prefixWord ++ tailWord_1218266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218266).length < 2 ^ (prefixWord ++ tailWord_1218266).sum := by decide
  have hdescent : baseEnd_1218266 < baseStart_1218266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218272 : List Nat := [2, 1, 1, 3, 1, 2, 4, 4, 5]
def baseStart_1218272 : Nat := 118140960795 + 1218272 * 2 ^ 59
def prefixEnd_1218272 : Nat := 4983230072969 + 3 ^ 40 * 1218272 * 2
def baseEnd_1218272 : Nat := 69506567101595859877475

theorem tailTrace_1218272 : CollatzResearch.WordTrace tailWord_1218272 prefixEnd_1218272 69506567101595859877475 := by
  unfold tailWord_1218272
  simp only [CollatzResearch.WordTrace]
  refine ⟨22217015121208041568932535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29622686828277388758576713 22217015121208041568932535)
  ·
    refine ⟨33325522681812062353398803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22217015121208041568932535 33325522681812062353398803)
    ·
      refine ⟨49988284022718093530098205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33325522681812062353398803 49988284022718093530098205)
      ·
        refine ⟨18745606508519285073786827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49988284022718093530098205 18745606508519285073786827)
        ·
          refine ⟨28118409762778927610680241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18745606508519285073786827 28118409762778927610680241)
          ·
            refine ⟨21088807322084195708010181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28118409762778927610680241 21088807322084195708010181)
            ·
              refine ⟨3954151372890786695251909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21088807322084195708010181 3954151372890786695251909)
              ·
                refine ⟨741403382417022505359733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3954151372890786695251909 741403382417022505359733)
                ·
                  refine ⟨69506567101595859877475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741403382417022505359733 69506567101595859877475)
                  ·
                    rfl

theorem cell23_1218272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 5].length) (baseStart_1218272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218272 prefixEnd_1218272 := by exact prefixLift 1218272
  have htrace : WordTrace (prefixWord ++ tailWord_1218272) baseStart_1218272 baseEnd_1218272 := by
    simpa [prefixWord, tailWord_1218272, baseEnd_1218272] using wordTrace_append hprefix tailTrace_1218272
  have hstable : (prefixWord ++ tailWord_1218272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218272).length < 2 ^ (prefixWord ++ tailWord_1218272).sum := by decide
  have hdescent : baseEnd_1218272 < baseStart_1218272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218282 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_1218282 : Nat := 118140960795 + 1218282 * 2 ^ 59
def prefixEnd_1218282 : Nat := 4983230072969 + 3 ^ 40 * 1218282 * 2
def baseEnd_1218282 : Nat := 625564238720907699772229

theorem tailTrace_1218282 : CollatzResearch.WordTrace tailWord_1218282 prefixEnd_1218282 625564238720907699772229 := by
  unfold tailWord_1218282
  simp only [CollatzResearch.WordTrace]
  refine ⟨11108598743094963711432275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29622929981586569897152733 11108598743094963711432275)
  ·
    refine ⟨16662898114642445567148413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11108598743094963711432275 16662898114642445567148413)
    ·
      refine ⟨6248586792990917087680655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16662898114642445567148413 6248586792990917087680655)
      ·
        refine ⟨9372880189486375631520983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6248586792990917087680655 9372880189486375631520983)
        ·
          refine ⟨14059320284229563447281475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9372880189486375631520983 14059320284229563447281475)
          ·
            refine ⟨21088980426344345170922213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14059320284229563447281475 21088980426344345170922213)
            ·
              refine ⟨3954183829939564719547915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21088980426344345170922213 3954183829939564719547915)
              ·
                refine ⟨5931275744909347079321873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954183829939564719547915 5931275744909347079321873)
                ·
                  refine ⟨4448456808682010309491405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5931275744909347079321873 4448456808682010309491405)
                  ·
                    refine ⟨1668171303255753866059277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4448456808682010309491405 1668171303255753866059277)
                    ·
                      refine ⟨625564238720907699772229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1668171303255753866059277 625564238720907699772229)
                      ·
                        rfl

theorem cell23_1218282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_1218282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218282 prefixEnd_1218282 := by exact prefixLift 1218282
  have htrace : WordTrace (prefixWord ++ tailWord_1218282) baseStart_1218282 baseEnd_1218282 := by
    simpa [prefixWord, tailWord_1218282, baseEnd_1218282] using wordTrace_append hprefix tailTrace_1218282
  have hstable : (prefixWord ++ tailWord_1218282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218282).length < 2 ^ (prefixWord ++ tailWord_1218282).sum := by decide
  have hdescent : baseEnd_1218282 < baseStart_1218282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218334 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1218334 : Nat := 118140960795 + 1218334 * 2 ^ 59
def prefixEnd_1218334 : Nat := 4983230072969 + 3 ^ 40 * 1218334 * 2
def baseEnd_1218334 : Nat := 625590939714941496321991

theorem tailTrace_1218334 : CollatzResearch.WordTrace tailWord_1218334 prefixEnd_1218334 625590939714941496321991 := by
  unfold tailWord_1218334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554536446023933465827757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29624194378794311817748037 5554536446023933465827757)
  ·
    refine ⟨2082951167258975049685409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5554536446023933465827757 2082951167258975049685409)
    ·
      refine ⟨1562213375444231287264057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2082951167258975049685409 1562213375444231287264057)
      ·
        refine ⟨1171660031583173465448043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1562213375444231287264057 1171660031583173465448043)
        ·
          refine ⟨1757490047374760198172065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171660031583173465448043 1757490047374760198172065)
          ·
            refine ⟨1318117535531070148629049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1757490047374760198172065 1318117535531070148629049)
            ·
              refine ⟨988588151648302611471787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318117535531070148629049 988588151648302611471787)
              ·
                refine ⟨1482882227472453917207681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988588151648302611471787 1482882227472453917207681)
                ·
                  refine ⟨1112161670604340437905761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1482882227472453917207681 1112161670604340437905761)
                  ·
                    refine ⟨834121252953255328429321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1112161670604340437905761 834121252953255328429321)
                    ·
                      refine ⟨625590939714941496321991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834121252953255328429321 625590939714941496321991)
                      ·
                        rfl

theorem cell23_1218334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1218334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218334 prefixEnd_1218334 := by exact prefixLift 1218334
  have htrace : WordTrace (prefixWord ++ tailWord_1218334) baseStart_1218334 baseEnd_1218334 := by
    simpa [prefixWord, tailWord_1218334, baseEnd_1218334] using wordTrace_append hprefix tailTrace_1218334
  have hstable : (prefixWord ++ tailWord_1218334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218334).length < 2 ^ (prefixWord ++ tailWord_1218334).sum := by decide
  have hdescent : baseEnd_1218334 < baseStart_1218334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218356 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1218356 : Nat := 118140960795 + 1218356 * 2 ^ 59
def prefixEnd_1218356 : Nat := 4983230072969 + 3 ^ 40 * 1218356 * 2
def baseEnd_1218356 : Nat := 625602236289340410246889

theorem tailTrace_1218356 : CollatzResearch.WordTrace tailWord_1218356 prefixEnd_1218356 625602236289340410246889 := by
  unfold tailWord_1218356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22218546987055882741961461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29624729316074510322615281 22218546987055882741961461)
  ·
    refine ⟨2082988780036489007058887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22218546987055882741961461 2082988780036489007058887)
    ·
      refine ⟨3124483170054733510588331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082988780036489007058887 3124483170054733510588331)
      ·
        refine ⟨4686724755082100265882497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3124483170054733510588331 4686724755082100265882497)
        ·
          refine ⟨3515043566311575199411873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4686724755082100265882497 3515043566311575199411873)
          ·
            refine ⟨2636282674733681399558905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3515043566311575199411873 2636282674733681399558905)
            ·
              refine ⟨1977212006050261049669179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2636282674733681399558905 1977212006050261049669179)
              ·
                refine ⟨2965818009075391574503769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977212006050261049669179 2965818009075391574503769)
                ·
                  refine ⟨2224363506806543680877827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2965818009075391574503769 2224363506806543680877827)
                  ·
                    refine ⟨3336545260209815521316741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2224363506806543680877827 3336545260209815521316741)
                    ·
                      refine ⟨625602236289340410246889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3336545260209815521316741 625602236289340410246889)
                      ·
                        rfl

theorem cell23_1218356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1218356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218356 prefixEnd_1218356 := by exact prefixLift 1218356
  have htrace : WordTrace (prefixWord ++ tailWord_1218356) baseStart_1218356 baseEnd_1218356 := by
    simpa [prefixWord, tailWord_1218356, baseEnd_1218356] using wordTrace_append hprefix tailTrace_1218356
  have hstable : (prefixWord ++ tailWord_1218356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218356).length < 2 ^ (prefixWord ++ tailWord_1218356).sum := by decide
  have hdescent : baseEnd_1218356 < baseStart_1218356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218410 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1218410 : Nat := 118140960795 + 1218410 * 2 ^ 59
def prefixEnd_1218410 : Nat := 4983230072969 + 3 ^ 40 * 1218410 * 2
def baseEnd_1218410 : Nat := 625629964244683198971641

theorem tailTrace_1218410 : CollatzResearch.WordTrace tailWord_1218410 prefixEnd_1218410 625629964244683198971641 := by
  unfold tailWord_1218410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11109765878979033176597171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29626042343944088470925789 11109765878979033176597171)
  ·
    refine ⟨16664648818468549764895757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11109765878979033176597171 16664648818468549764895757)
    ·
      refine ⟨6249243306925706161835909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16664648818468549764895757 6249243306925706161835909)
      ·
        refine ⟨1171733120048569905344233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6249243306925706161835909 1171733120048569905344233)
        ·
          refine ⟨878799840036427429008175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1171733120048569905344233 878799840036427429008175)
          ·
            refine ⟨1318199760054641143512263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878799840036427429008175 1318199760054641143512263)
            ·
              refine ⟨1977299640081961715268395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318199760054641143512263 1977299640081961715268395)
              ·
                refine ⟨2965949460122942572902593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977299640081961715268395 2965949460122942572902593)
                ·
                  refine ⟨2224462095092206929676945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2965949460122942572902593 2224462095092206929676945)
                  ·
                    refine ⟨1668346571319155197257709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2224462095092206929676945 1668346571319155197257709)
                    ·
                      refine ⟨625629964244683198971641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1668346571319155197257709 625629964244683198971641)
                      ·
                        rfl

theorem cell23_1218410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1218410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218410 prefixEnd_1218410 := by exact prefixLift 1218410
  have htrace : WordTrace (prefixWord ++ tailWord_1218410) baseStart_1218410 baseEnd_1218410 := by
    simpa [prefixWord, tailWord_1218410, baseEnd_1218410] using wordTrace_append hprefix tailTrace_1218410
  have hstable : (prefixWord ++ tailWord_1218410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218410).length < 2 ^ (prefixWord ++ tailWord_1218410).sum := by decide
  have hdescent : baseEnd_1218410 < baseStart_1218410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218432 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_1218432 : Nat := 118140960795 + 1218432 * 2 ^ 59
def prefixEnd_1218432 : Nat := 4983230072969 + 3 ^ 40 * 1218432 * 2
def baseEnd_1218432 : Nat := 625641260819082112896539

theorem tailTrace_1218432 : CollatzResearch.WordTrace tailWord_1218432 prefixEnd_1218432 625641260819082112896539 := by
  unfold tailWord_1218432
  simp only [CollatzResearch.WordTrace]
  refine ⟨22219932960918215231844775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29626577281224286975793033 22219932960918215231844775)
  ·
    refine ⟨33329899441377322847767163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22219932960918215231844775 33329899441377322847767163)
    ·
      refine ⟨49994849162065984271650745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33329899441377322847767163 49994849162065984271650745)
      ·
        refine ⟨37496136871549488203738059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49994849162065984271650745 37496136871549488203738059)
        ·
          refine ⟨56244205307324232305607089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37496136871549488203738059 56244205307324232305607089)
          ·
            refine ⟨42183153980493174229205317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56244205307324232305607089 42183153980493174229205317)
            ·
              refine ⟨7909341371342470167975997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42183153980493174229205317 7909341371342470167975997)
              ·
                refine ⟨2966003014253426312990999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7909341371342470167975997 2966003014253426312990999)
                ·
                  refine ⟨4449004521380139469486499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966003014253426312990999 4449004521380139469486499)
                  ·
                    refine ⟨6673506782070209204229749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4449004521380139469486499 6673506782070209204229749)
                    ·
                      refine ⟨625641260819082112896539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6673506782070209204229749 625641260819082112896539)
                      ·
                        rfl

theorem cell23_1218432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_1218432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218432 prefixEnd_1218432 := by exact prefixLift 1218432
  have htrace : WordTrace (prefixWord ++ tailWord_1218432) baseStart_1218432 baseEnd_1218432 := by
    simpa [prefixWord, tailWord_1218432, baseEnd_1218432] using wordTrace_append hprefix tailTrace_1218432
  have hstable : (prefixWord ++ tailWord_1218432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218432).length < 2 ^ (prefixWord ++ tailWord_1218432).sum := by decide
  have hdescent : baseEnd_1218432 < baseStart_1218432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218479 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 3]
def baseStart_1218479 : Nat := 118140960795 + 1218479 * 2 ^ 59
def prefixEnd_1218479 : Nat := 4983230072969 + 3 ^ 40 * 1218479 * 2
def baseEnd_1218479 : Nat := 625665394409843429008823

theorem tailTrace_1218479 : CollatzResearch.WordTrace tailWord_1218479 prefixEnd_1218479 625665394409843429008823 := by
  unfold tailWord_1218479
  simp only [CollatzResearch.WordTrace]
  refine ⟨44441580152666157490650491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29627720101777438327100327 44441580152666157490650491)
  ·
    refine ⟨66662370228999236235975737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44441580152666157490650491 66662370228999236235975737)
    ·
      refine ⟨49996777671749427176981803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66662370228999236235975737 49996777671749427176981803)
      ·
        refine ⟨74995166507624140765472705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49996777671749427176981803 74995166507624140765472705)
        ·
          refine ⟨56246374880718105574104529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74995166507624140765472705 56246374880718105574104529)
          ·
            refine ⟨42184781160538579180578397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56246374880718105574104529 42184781160538579180578397)
            ·
              refine ⟨15819292935201967192716899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42184781160538579180578397 15819292935201967192716899)
              ·
                refine ⟨23728939402802950789075349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15819292935201967192716899 23728939402802950789075349)
                ·
                  refine ⟨1112294034506388318237907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23728939402802950789075349 1112294034506388318237907)
                  ·
                    refine ⟨1668441051759582477356861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1112294034506388318237907 1668441051759582477356861)
                    ·
                      refine ⟨625665394409843429008823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1668441051759582477356861 625665394409843429008823)
                      ·
                        rfl

theorem cell23_1218479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 1, 3].length) (baseStart_1218479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218479 prefixEnd_1218479 := by exact prefixLift 1218479
  have htrace : WordTrace (prefixWord ++ tailWord_1218479) baseStart_1218479 baseEnd_1218479 := by
    simpa [prefixWord, tailWord_1218479, baseEnd_1218479] using wordTrace_append hprefix tailTrace_1218479
  have hstable : (prefixWord ++ tailWord_1218479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218479).length < 2 ^ (prefixWord ++ tailWord_1218479).sum := by decide
  have hdescent : baseEnd_1218479 < baseStart_1218479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218496 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 2, 1, 3]
def baseStart_1218496 : Nat := 118140960795 + 1218496 * 2 ^ 59
def prefixEnd_1218496 : Nat := 4983230072969 + 3 ^ 40 * 1218496 * 2
def baseEnd_1218496 : Nat := 625674123580969862496245

theorem tailTrace_1218496 : CollatzResearch.WordTrace tailWord_1218496 prefixEnd_1218496 625674123580969862496245 := by
  unfold tailWord_1218496
  simp only [CollatzResearch.WordTrace]
  refine ⟨22221100096802284697009671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29628133462403046262679561 22221100096802284697009671)
  ·
    refine ⟨33331650145203427045514507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22221100096802284697009671 33331650145203427045514507)
    ·
      refine ⟨49997475217805140568271761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33331650145203427045514507 49997475217805140568271761)
      ·
        refine ⟨37498106413353855426203821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49997475217805140568271761 37498106413353855426203821)
        ·
          refine ⟨14061789905007695784826433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37498106413353855426203821 14061789905007695784826433)
          ·
            refine ⟨10546342428755771838619825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14061789905007695784826433 10546342428755771838619825)
            ·
              refine ⟨7909756821566828878964869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10546342428755771838619825 7909756821566828878964869)
              ·
                refine ⟨1483079404043780414805913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7909756821566828878964869 1483079404043780414805913)
                ·
                  refine ⟨1112309553032835311104435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1483079404043780414805913 1112309553032835311104435)
                  ·
                    refine ⟨1668464329549252966656653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1112309553032835311104435 1668464329549252966656653)
                    ·
                      refine ⟨625674123580969862496245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1668464329549252966656653 625674123580969862496245)
                      ·
                        rfl

theorem cell23_1218496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_1218496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218496 prefixEnd_1218496 := by exact prefixLift 1218496
  have htrace : WordTrace (prefixWord ++ tailWord_1218496) baseStart_1218496 baseEnd_1218496 := by
    simpa [prefixWord, tailWord_1218496, baseEnd_1218496] using wordTrace_append hprefix tailTrace_1218496
  have hstable : (prefixWord ++ tailWord_1218496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218496).length < 2 ^ (prefixWord ++ tailWord_1218496).sum := by decide
  have hdescent : baseEnd_1218496 < baseStart_1218496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218512 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 2, 6]
def baseStart_1218512 : Nat := 118140960795 + 1218512 * 2 ^ 59
def prefixEnd_1218512 : Nat := 4983230072969 + 3 ^ 40 * 1218512 * 2
def baseEnd_1218512 : Nat := 208560779757147266632057

theorem tailTrace_1218512 : CollatzResearch.WordTrace tailWord_1218512 prefixEnd_1218512 208560779757147266632057 := by
  unfold tailWord_1218512
  simp only [CollatzResearch.WordTrace]
  refine ⟨22221391880773302063300895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29628522507697736084401193 22221391880773302063300895)
  ·
    refine ⟨33332087821159953094951343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22221391880773302063300895 33332087821159953094951343)
    ·
      refine ⟨49998131731739929642427015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33332087821159953094951343 49998131731739929642427015)
      ·
        refine ⟨74997197597609894463640523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49998131731739929642427015 74997197597609894463640523)
        ·
          refine ⟨112495796396414841695460785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74997197597609894463640523 112495796396414841695460785)
          ·
            refine ⟨84371847297311131271595589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112495796396414841695460785 84371847297311131271595589)
            ·
              refine ⟨15819721368245837113424173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84371847297311131271595589 15819721368245837113424173)
              ·
                refine ⟨5932395513092188917534065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15819721368245837113424173 5932395513092188917534065)
                ·
                  refine ⟨4449296634819141688150549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5932395513092188917534065 4449296634819141688150549)
                  ·
                    refine ⟨208560779757147266632057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4449296634819141688150549 208560779757147266632057)
                    ·
                      rfl

theorem cell23_1218512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_1218512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218512 prefixEnd_1218512 := by exact prefixLift 1218512
  have htrace : WordTrace (prefixWord ++ tailWord_1218512) baseStart_1218512 baseEnd_1218512 := by
    simpa [prefixWord, tailWord_1218512, baseEnd_1218512] using wordTrace_append hprefix tailTrace_1218512
  have hstable : (prefixWord ++ tailWord_1218512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218512).length < 2 ^ (prefixWord ++ tailWord_1218512).sum := by decide
  have hdescent : baseEnd_1218512 < baseStart_1218512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218552 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_1218552 : Nat := 118140960795 + 1218552 * 2 ^ 59
def prefixEnd_1218552 : Nat := 4983230072969 + 3 ^ 40 * 1218552 * 2
def baseEnd_1218552 : Nat := 625702878497621643395987

theorem tailTrace_1218552 : CollatzResearch.WordTrace tailWord_1218552 prefixEnd_1218552 625702878497621643395987 := by
  unfold tailWord_1218552
  simp only [CollatzResearch.WordTrace]
  refine ⟨22222121340700845479028955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29629495120934460638705273 22222121340700845479028955)
  ·
    refine ⟨33333182011051268218543433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22222121340700845479028955 33333182011051268218543433)
    ·
      refine ⟨24999886508288451163907575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33333182011051268218543433 24999886508288451163907575)
      ·
        refine ⟨37499829762432676745861363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24999886508288451163907575 37499829762432676745861363)
        ·
          refine ⟨56249744643649015118792045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37499829762432676745861363 56249744643649015118792045)
          ·
            refine ⟨21093654241368380669547017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56249744643649015118792045 21093654241368380669547017)
            ·
              refine ⟨15820240681026285502160263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21093654241368380669547017 15820240681026285502160263)
              ·
                refine ⟨23730361021539428253240395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15820240681026285502160263 23730361021539428253240395)
                ·
                  refine ⟨35595541532309142379860593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23730361021539428253240395 35595541532309142379860593)
                  ·
                    refine ⟨26696656149231856784895445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35595541532309142379860593 26696656149231856784895445)
                    ·
                      refine ⟨625702878497621643395987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 26696656149231856784895445 625702878497621643395987)
                      ·
                        rfl

theorem cell23_1218552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_1218552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218552 prefixEnd_1218552 := by exact prefixLift 1218552
  have htrace : WordTrace (prefixWord ++ tailWord_1218552) baseStart_1218552 baseEnd_1218552 := by
    simpa [prefixWord, tailWord_1218552, baseEnd_1218552] using wordTrace_append hprefix tailTrace_1218552
  have hstable : (prefixWord ++ tailWord_1218552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218552).length < 2 ^ (prefixWord ++ tailWord_1218552).sum := by decide
  have hdescent : baseEnd_1218552 < baseStart_1218552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218553 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 2, 2, 2]
def baseStart_1218553 : Nat := 118140960795 + 1218553 * 2 ^ 59
def prefixEnd_1218553 : Nat := 4983230072969 + 3 ^ 40 * 1218553 * 2
def baseEnd_1218553 : Nat := 625703391978276139483483

theorem tailTrace_1218553 : CollatzResearch.WordTrace tailWord_1218553 prefixEnd_1218553 625703391978276139483483 := by
  unfold tailWord_1218553
  simp only [CollatzResearch.WordTrace]
  refine ⟨44444279154398068128844313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29629519436265378752562875 44444279154398068128844313)
  ·
    refine ⟨33333209365798551096633235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44444279154398068128844313 33333209365798551096633235)
    ·
      refine ⟨49999814048697826644949853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33333209365798551096633235 49999814048697826644949853)
      ·
        refine ⟨18749930268261684991856195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49999814048697826644949853 18749930268261684991856195)
        ·
          refine ⟨28124895402392527487784293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18749930268261684991856195 28124895402392527487784293)
          ·
            refine ⟨5273417887948598903959555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28124895402392527487784293 5273417887948598903959555)
            ·
              refine ⟨7910126831922898355939333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273417887948598903959555 7910126831922898355939333)
              ·
                refine ⟨1483148780985543441738625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7910126831922898355939333 1483148780985543441738625)
                ·
                  refine ⟨1112361585739157581303969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1483148780985543441738625 1112361585739157581303969)
                  ·
                    refine ⟨834271189304368185977977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1112361585739157581303969 834271189304368185977977)
                    ·
                      refine ⟨625703391978276139483483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 834271189304368185977977 625703391978276139483483)
                      ·
                        rfl

theorem cell23_1218553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_1218553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218553 prefixEnd_1218553 := by exact prefixLift 1218553
  have htrace : WordTrace (prefixWord ++ tailWord_1218553) baseStart_1218553 baseEnd_1218553 := by
    simpa [prefixWord, tailWord_1218553, baseEnd_1218553] using wordTrace_append hprefix tailTrace_1218553
  have hstable : (prefixWord ++ tailWord_1218553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218553).length < 2 ^ (prefixWord ++ tailWord_1218553).sum := by decide
  have hdescent : baseEnd_1218553 < baseStart_1218553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218593 : List Nat := [1, 2, 3, 2, 4, 1, 2, 3, 5]
def baseStart_1218593 : Nat := 118140960795 + 1218593 * 2 ^ 59
def prefixEnd_1218593 : Nat := 4983230072969 + 3 ^ 40 * 1218593 * 2
def baseEnd_1218593 : Nat := 69524881244939553664811

theorem tailTrace_1218593 : CollatzResearch.WordTrace tailWord_1218593 prefixEnd_1218593 69524881244939553664811 := by
  unfold tailWord_1218593
  simp only [CollatzResearch.WordTrace]
  refine ⟨44445738074253154960300433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29630492049502103306866955 44445738074253154960300433)
  ·
    refine ⟨33334303555689866220225325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44445738074253154960300433 33334303555689866220225325)
    ·
      refine ⟨12500363833383699832584497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33334303555689866220225325 12500363833383699832584497)
      ·
        refine ⟨9375272875037774874438373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12500363833383699832584497 9375272875037774874438373)
        ·
          refine ⟨1757863664069582788957195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9375272875037774874438373 1757863664069582788957195)
          ·
            refine ⟨2636795496104374183435793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757863664069582788957195 2636795496104374183435793)
            ·
              refine ⟨1977596622078280637576845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2636795496104374183435793 1977596622078280637576845)
              ·
                refine ⟨741598733279355239091317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1977596622078280637576845 741598733279355239091317)
                ·
                  refine ⟨69524881244939553664811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 741598733279355239091317 69524881244939553664811)
                  ·
                    rfl

theorem cell23_1218593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 5].length) (baseStart_1218593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218593 prefixEnd_1218593 := by exact prefixLift 1218593
  have htrace : WordTrace (prefixWord ++ tailWord_1218593) baseStart_1218593 baseEnd_1218593 := by
    simpa [prefixWord, tailWord_1218593, baseEnd_1218593] using wordTrace_append hprefix tailTrace_1218593
  have hstable : (prefixWord ++ tailWord_1218593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218593).length < 2 ^ (prefixWord ++ tailWord_1218593).sum := by decide
  have hdescent : baseEnd_1218593 < baseStart_1218593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218619 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 7, 4]
def baseStart_1218619 : Nat := 118140960795 + 1218619 * 2 ^ 59
def prefixEnd_1218619 : Nat := 4983230072969 + 3 ^ 40 * 1218619 * 2
def baseEnd_1218619 : Nat := 208579093900490960419393

theorem tailTrace_1218619 : CollatzResearch.WordTrace tailWord_1218619 prefixEnd_1218619 208579093900490960419393 := by
  unfold tailWord_1218619
  simp only [CollatzResearch.WordTrace]
  refine ⟨44446686372158961400746911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29631124248105974267164607 44446686372158961400746911)
  ·
    refine ⟨66670029558238442101120367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44446686372158961400746911 66670029558238442101120367)
    ·
      refine ⟨100005044337357663151680551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66670029558238442101120367 100005044337357663151680551)
      ·
        refine ⟨150007566506036494727520827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100005044337357663151680551 150007566506036494727520827)
        ·
          refine ⟨225011349759054742091281241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150007566506036494727520827 225011349759054742091281241)
          ·
            refine ⟨168758512319291056568460931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225011349759054742091281241 168758512319291056568460931)
            ·
              refine ⟨253137768478936584852691397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168758512319291056568460931 253137768478936584852691397)
              ·
                refine ⟨47463331589800609659879637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 253137768478936584852691397 47463331589800609659879637)
                ·
                  refine ⟨1112421834135951788903429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 47463331589800609659879637 1112421834135951788903429)
                  ·
                    refine ⟨208579093900490960419393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1112421834135951788903429 208579093900490960419393)
                    ·
                      rfl

theorem cell23_1218619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 4].length) (baseStart_1218619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218619 prefixEnd_1218619 := by exact prefixLift 1218619
  have htrace : WordTrace (prefixWord ++ tailWord_1218619) baseStart_1218619 baseEnd_1218619 := by
    simpa [prefixWord, tailWord_1218619, baseEnd_1218619] using wordTrace_append hprefix tailTrace_1218619
  have hstable : (prefixWord ++ tailWord_1218619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218619).length < 2 ^ (prefixWord ++ tailWord_1218619).sum := by decide
  have hdescent : baseEnd_1218619 < baseStart_1218619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218636 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_1218636 : Nat := 118140960795 + 1218636 * 2 ^ 59
def prefixEnd_1218636 : Nat := 4983230072969 + 3 ^ 40 * 1218636 * 2
def baseEnd_1218636 : Nat := 208582003624199771581867

theorem tailTrace_1218636 : CollatzResearch.WordTrace tailWord_1218636 prefixEnd_1218636 208582003624199771581867 := by
  unfold tailWord_1218636
  simp only [CollatzResearch.WordTrace]
  refine ⟨22223653206548686652057881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29631537608731582202743841 22223653206548686652057881)
  ·
    refine ⟨16667739904911514989043411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22223653206548686652057881 16667739904911514989043411)
    ·
      refine ⟨25001609857367272483565117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16667739904911514989043411 25001609857367272483565117)
      ·
        refine ⟨9375603696512727181336919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25001609857367272483565117 9375603696512727181336919)
        ·
          refine ⟨14063405544769090772005379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9375603696512727181336919 14063405544769090772005379)
          ·
            refine ⟨21095108317153636158008069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14063405544769090772005379 21095108317153636158008069)
            ·
              refine ⟨3955332809466306779626513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21095108317153636158008069 3955332809466306779626513)
              ·
                refine ⟨2966499607099730084719885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3955332809466306779626513 2966499607099730084719885)
                ·
                  refine ⟨1112437352662398781769957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2966499607099730084719885 1112437352662398781769957)
                  ·
                    refine ⟨208582003624199771581867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1112437352662398781769957 208582003624199771581867)
                    ·
                      rfl

theorem cell23_1218636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_1218636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218636 prefixEnd_1218636 := by exact prefixLift 1218636
  have htrace : WordTrace (prefixWord ++ tailWord_1218636) baseStart_1218636 baseEnd_1218636 := by
    simpa [prefixWord, tailWord_1218636, baseEnd_1218636] using wordTrace_append hprefix tailTrace_1218636
  have hstable : (prefixWord ++ tailWord_1218636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218636).length < 2 ^ (prefixWord ++ tailWord_1218636).sum := by decide
  have hdescent : baseEnd_1218636 < baseStart_1218636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218729 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_1218729 : Nat := 118140960795 + 1218729 * 2 ^ 59
def prefixEnd_1218729 : Nat := 4983230072969 + 3 ^ 40 * 1218729 * 2
def baseEnd_1218729 : Nat := 625793764573467450882673

theorem tailTrace_1218729 : CollatzResearch.WordTrace tailWord_1218729 prefixEnd_1218729 625793764573467450882673 := by
  unfold tailWord_1218729
  simp only [CollatzResearch.WordTrace]
  refine ⟨44450698401760450187251241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29633798934506966791500827 44450698401760450187251241)
  ·
    refine ⟨33338023801320337640438431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44450698401760450187251241 33338023801320337640438431)
    ·
      refine ⟨50007035701980506460657647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33338023801320337640438431 50007035701980506460657647)
      ·
        refine ⟨75010553552970759690986471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50007035701980506460657647 75010553552970759690986471)
        ·
          refine ⟨112515830329456139536479707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75010553552970759690986471 112515830329456139536479707)
          ·
            refine ⟨168773745494184209304719561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112515830329456139536479707 168773745494184209304719561)
            ·
              refine ⟨126580309120638156978539671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168773745494184209304719561 126580309120638156978539671)
              ·
                refine ⟨189870463680957235467809507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126580309120638156978539671 189870463680957235467809507)
                ·
                  refine ⟨284805695521435853201714261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189870463680957235467809507 284805695521435853201714261)
                  ·
                    refine ⟨3337566744391826404707589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 284805695521435853201714261 3337566744391826404707589)
                    ·
                      refine ⟨625793764573467450882673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3337566744391826404707589 625793764573467450882673)
                      ·
                        rfl

theorem cell23_1218729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_1218729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218729 prefixEnd_1218729 := by exact prefixLift 1218729
  have htrace : WordTrace (prefixWord ++ tailWord_1218729) baseStart_1218729 baseEnd_1218729 := by
    simpa [prefixWord, tailWord_1218729, baseEnd_1218729] using wordTrace_append hprefix tailTrace_1218729
  have hstable : (prefixWord ++ tailWord_1218729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218729).length < 2 ^ (prefixWord ++ tailWord_1218729).sum := by decide
  have hdescent : baseEnd_1218729 < baseStart_1218729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218733 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1218733 : Nat := 118140960795 + 1218733 * 2 ^ 59
def prefixEnd_1218733 : Nat := 4983230072969 + 3 ^ 40 * 1218733 * 2
def baseEnd_1218733 : Nat := 625795818496085435232655

theorem tailTrace_1218733 : CollatzResearch.WordTrace tailWord_1218733 prefixEnd_1218733 625795818496085435232655 := by
  unfold tailWord_1218733
  simp only [CollatzResearch.WordTrace]
  refine ⟨44450844293745958870396853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29633896195830639246931235 44450844293745958870396853)
  ·
    refine ⟨4167266652538683644099705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44450844293745958870396853 4167266652538683644099705)
    ·
      refine ⟨3125449989404012733074779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4167266652538683644099705 3125449989404012733074779)
      ·
        refine ⟨4688174984106019099612169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125449989404012733074779 4688174984106019099612169)
        ·
          refine ⟨3516131238079514324709127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4688174984106019099612169 3516131238079514324709127)
          ·
            refine ⟨5274196857119271487063691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516131238079514324709127 5274196857119271487063691)
            ·
              refine ⟨7911295285678907230595537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274196857119271487063691 7911295285678907230595537)
              ·
                refine ⟨5933471464259180422946653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7911295285678907230595537 5933471464259180422946653)
                ·
                  refine ⟨2225051799097192658604995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5933471464259180422946653 2225051799097192658604995)
                  ·
                    refine ⟨3337577698645788987907493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2225051799097192658604995 3337577698645788987907493)
                    ·
                      refine ⟨625795818496085435232655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3337577698645788987907493 625795818496085435232655)
                      ·
                        rfl

theorem cell23_1218733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1218733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218733 prefixEnd_1218733 := by exact prefixLift 1218733
  have htrace : WordTrace (prefixWord ++ tailWord_1218733) baseStart_1218733 baseEnd_1218733 := by
    simpa [prefixWord, tailWord_1218733, baseEnd_1218733] using wordTrace_append hprefix tailTrace_1218733
  have hstable : (prefixWord ++ tailWord_1218733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218733).length < 2 ^ (prefixWord ++ tailWord_1218733).sum := by decide
  have hdescent : baseEnd_1218733 < baseStart_1218733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218743 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 2, 4]
def baseStart_1218743 : Nat := 118140960795 + 1218743 * 2 ^ 59
def prefixEnd_1218743 : Nat := 4983230072969 + 3 ^ 40 * 1218743 * 2
def baseEnd_1218743 : Nat := 208600317767543465369203

theorem tailTrace_1218743 : CollatzResearch.WordTrace tailWord_1218743 prefixEnd_1218743 208600317767543465369203 := by
  unfold tailWord_1218743
  simp only [CollatzResearch.WordTrace]
  refine ⟨44451209023709730578260883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29634139349139820385507255 44451209023709730578260883)
  ·
    refine ⟨66676813535564595867391325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44451209023709730578260883 66676813535564595867391325)
    ·
      refine ⟨25003805075836723450271747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66676813535564595867391325 25003805075836723450271747)
      ·
        refine ⟨37505707613755085175407621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25003805075836723450271747 37505707613755085175407621)
        ·
          refine ⟨7032320177579078470388929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37505707613755085175407621 7032320177579078470388929)
          ·
            refine ⟨5274240133184308852791697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7032320177579078470388929 5274240133184308852791697)
            ·
              refine ⟨3955680099888231639593773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5274240133184308852791697 3955680099888231639593773)
              ·
                refine ⟨1483380037458086864847665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3955680099888231639593773 1483380037458086864847665)
                ·
                  refine ⟨1112535028093565148635749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1483380037458086864847665 1112535028093565148635749)
                  ·
                    refine ⟨208600317767543465369203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1112535028093565148635749 208600317767543465369203)
                    ·
                      rfl

theorem cell23_1218743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_1218743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218743 prefixEnd_1218743 := by exact prefixLift 1218743
  have htrace : WordTrace (prefixWord ++ tailWord_1218743) baseStart_1218743 baseEnd_1218743 := by
    simpa [prefixWord, tailWord_1218743, baseEnd_1218743] using wordTrace_append hprefix tailTrace_1218743
  have hstable : (prefixWord ++ tailWord_1218743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218743).length < 2 ^ (prefixWord ++ tailWord_1218743).sum := by decide
  have hdescent : baseEnd_1218743 < baseStart_1218743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218746 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_1218746 : Nat := 118140960795 + 1218746 * 2 ^ 59
def prefixEnd_1218746 : Nat := 4983230072969 + 3 ^ 40 * 1218746 * 2
def baseEnd_1218746 : Nat := 625802493744593884370095

theorem tailTrace_1218746 : CollatzResearch.WordTrace tailWord_1218746 prefixEnd_1218746 625802493744593884370095 := by
  unfold tailWord_1218746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11112829610674715522655023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29634212295132574727080061 11112829610674715522655023)
  ·
    refine ⟨16669244416012073283982535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11112829610674715522655023 16669244416012073283982535)
    ·
      refine ⟨25003866624018109925973803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16669244416012073283982535 25003866624018109925973803)
      ·
        refine ⟨37505799936027164888960705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25003866624018109925973803 37505799936027164888960705)
        ·
          refine ⟨28129349952020373666720529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37505799936027164888960705 28129349952020373666720529)
          ·
            refine ⟨21097012464015280250040397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28129349952020373666720529 21097012464015280250040397)
            ·
              refine ⟨7911379674005730093765149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21097012464015280250040397 7911379674005730093765149)
              ·
                refine ⟨2966767377752148785161931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7911379674005730093765149 2966767377752148785161931)
                ·
                  refine ⟨4450151066628223177742897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966767377752148785161931 4450151066628223177742897)
                  ·
                    refine ⟨3337613299971167383307173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4450151066628223177742897 3337613299971167383307173)
                    ·
                      refine ⟨625802493744593884370095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3337613299971167383307173 625802493744593884370095)
                      ·
                        rfl

theorem cell23_1218746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_1218746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1218746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1218746 prefixEnd_1218746 := by exact prefixLift 1218746
  have htrace : WordTrace (prefixWord ++ tailWord_1218746) baseStart_1218746 baseEnd_1218746 := by
    simpa [prefixWord, tailWord_1218746, baseEnd_1218746] using wordTrace_append hprefix tailTrace_1218746
  have hstable : (prefixWord ++ tailWord_1218746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218746).length < 2 ^ (prefixWord ++ tailWord_1218746).sum := by decide
  have hdescent : baseEnd_1218746 < baseStart_1218746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
