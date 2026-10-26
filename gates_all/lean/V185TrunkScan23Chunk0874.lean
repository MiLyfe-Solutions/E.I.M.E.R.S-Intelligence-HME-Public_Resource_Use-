import V185TrunkScan23Chunk0873

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5172628 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_5172628 : Nat := 118140960795 + 5172628 * 2 ^ 59
def prefixEnd_5172628 : Nat := 4983230072969 + 3 ^ 40 * 5172628 * 2
def baseEnd_5172628 : Nat := 2656044410904893302861523

theorem tailTrace_5172628 : CollatzResearch.WordTrace tailWord_5172628 prefixEnd_5172628 2656044410904893302861523 := by
  unfold tailWord_5172628
  simp only [CollatzResearch.WordTrace]
  refine ⟨94330621152229822687643269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125774161536306430250191025 94330621152229822687643269)
  ·
    refine ⟨17686991466043091753933113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94330621152229822687643269 17686991466043091753933113)
    ·
      refine ⟨13265243599532318815449835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17686991466043091753933113 13265243599532318815449835)
      ·
        refine ⟨19897865399298478223174753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13265243599532318815449835 19897865399298478223174753)
        ·
          refine ⟨14923399049473858667381065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19897865399298478223174753 14923399049473858667381065)
          ·
            refine ⟨11192549287105394000535799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14923399049473858667381065 11192549287105394000535799)
            ·
              refine ⟨16788823930658091000803699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11192549287105394000535799 16788823930658091000803699)
              ·
                refine ⟨25183235895987136501205549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16788823930658091000803699 25183235895987136501205549)
                ·
                  refine ⟨9443713460995176187952081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25183235895987136501205549 9443713460995176187952081)
                  ·
                    refine ⟨7082785095746382140964061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9443713460995176187952081 7082785095746382140964061)
                    ·
                      refine ⟨2656044410904893302861523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7082785095746382140964061 2656044410904893302861523)
                      ·
                        rfl

theorem cell23_5172628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_5172628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172628 prefixEnd_5172628 := by exact prefixLift 5172628
  have htrace : WordTrace (prefixWord ++ tailWord_5172628) baseStart_5172628 baseEnd_5172628 := by
    simpa [prefixWord, tailWord_5172628, baseEnd_5172628] using wordTrace_append hprefix tailTrace_5172628
  have hstable : (prefixWord ++ tailWord_5172628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172628).length < 2 ^ (prefixWord ++ tailWord_5172628).sum := by decide
  have hdescent : baseEnd_5172628 < baseStart_5172628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172664 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 2, 3, 4]
def baseStart_5172664 : Nat := 118140960795 + 5172664 * 2 ^ 59
def prefixEnd_5172664 : Nat := 4983230072969 + 3 ^ 40 * 5172664 * 2
def baseEnd_5172664 : Nat := 2656062896208455162011357

theorem tailTrace_5172664 : CollatzResearch.WordTrace tailWord_5172664 prefixEnd_5172664 2656062896208455162011357 := by
  unfold tailWord_5172664
  simp only [CollatzResearch.WordTrace]
  refine ⟨94331277666164611761798523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125775036888219482349064697 94331277666164611761798523)
  ·
    refine ⟨141496916499246917642697785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94331277666164611761798523 141496916499246917642697785)
    ·
      refine ⟨106122687374435188232023339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141496916499246917642697785 106122687374435188232023339)
      ·
        refine ⟨159184031061652782348035009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106122687374435188232023339 159184031061652782348035009)
        ·
          refine ⟨119388023296239586761026257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159184031061652782348035009 119388023296239586761026257)
          ·
            refine ⟨89541017472179690070769693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119388023296239586761026257 89541017472179690070769693)
            ·
              refine ⟨33577881552067383776538635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89541017472179690070769693 33577881552067383776538635)
              ·
                refine ⟨50366822328101075664807953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33577881552067383776538635 50366822328101075664807953)
                ·
                  refine ⟨37775116746075806748605965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50366822328101075664807953 37775116746075806748605965)
                  ·
                    refine ⟨14165668779778427530727237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37775116746075806748605965 14165668779778427530727237)
                    ·
                      refine ⟨2656062896208455162011357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14165668779778427530727237 2656062896208455162011357)
                      ·
                        rfl

theorem cell23_5172664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_5172664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172664 prefixEnd_5172664 := by exact prefixLift 5172664
  have htrace : WordTrace (prefixWord ++ tailWord_5172664) baseStart_5172664 baseEnd_5172664 := by
    simpa [prefixWord, tailWord_5172664, baseEnd_5172664] using wordTrace_append hprefix tailTrace_5172664
  have hstable : (prefixWord ++ tailWord_5172664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172664).length < 2 ^ (prefixWord ++ tailWord_5172664).sum := by decide
  have hdescent : baseEnd_5172664 < baseStart_5172664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172698 : List Nat := [3, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2]
def baseStart_5172698 : Nat := 118140960795 + 5172698 * 2 ^ 59
def prefixEnd_5172698 : Nat := 4983230072969 + 3 ^ 40 * 5172698 * 2
def baseEnd_5172698 : Nat := 2656080354550708028986201

theorem tailTrace_5172698 : CollatzResearch.WordTrace tailWord_5172698 prefixEnd_5172698 2656080354550708028986201 := by
  unfold tailWord_5172698
  simp only [CollatzResearch.WordTrace]
  refine ⟨47165948853551511832583687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125775863609470698220223165 47165948853551511832583687)
  ·
    refine ⟨70748923280327267748875531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47165948853551511832583687 70748923280327267748875531)
    ·
      refine ⟨106123384920490901623313297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70748923280327267748875531 106123384920490901623313297)
      ·
        refine ⟨79592538690368176217484973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106123384920490901623313297 79592538690368176217484973)
        ·
          refine ⟨29847202008888066081556865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79592538690368176217484973 29847202008888066081556865)
          ·
            refine ⟨22385401506666049561167649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29847202008888066081556865 22385401506666049561167649)
            ·
              refine ⟨16789051129999537170875737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22385401506666049561167649 16789051129999537170875737)
              ·
                refine ⟨12591788347499652878156803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16789051129999537170875737 12591788347499652878156803)
                ·
                  refine ⟨18887682521249479317235205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12591788347499652878156803 18887682521249479317235205)
                  ·
                    refine ⟨3541440472734277371981601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18887682521249479317235205 3541440472734277371981601)
                    ·
                      refine ⟨2656080354550708028986201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541440472734277371981601 2656080354550708028986201)
                      ·
                        rfl

theorem cell23_5172698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_5172698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172698 prefixEnd_5172698 := by exact prefixLift 5172698
  have htrace : WordTrace (prefixWord ++ tailWord_5172698) baseStart_5172698 baseEnd_5172698 := by
    simpa [prefixWord, tailWord_5172698, baseEnd_5172698] using wordTrace_append hprefix tailTrace_5172698
  have hstable : (prefixWord ++ tailWord_5172698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172698).length < 2 ^ (prefixWord ++ tailWord_5172698).sum := by decide
  have hdescent : baseEnd_5172698 < baseStart_5172698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172711 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_5172711 : Nat := 118140960795 + 5172711 * 2 ^ 59
def prefixEnd_5172711 : Nat := 4983230072969 + 3 ^ 40 * 5172711 * 2
def baseEnd_5172711 : Nat := 2656087029799216478123641

theorem tailTrace_5172711 : CollatzResearch.WordTrace tailWord_5172711 prefixEnd_5172711 2656087029799216478123641 := by
  unfold tailWord_5172711
  simp only [CollatzResearch.WordTrace]
  refine ⟨188664269563158950550557987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125776179708772633700371991 188664269563158950550557987)
  ·
    refine ⟨282996404344738425825836981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188664269563158950550557987 282996404344738425825836981)
    ·
      refine ⟨26530912907319227421172217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 282996404344738425825836981 26530912907319227421172217)
      ·
        refine ⟨19898184680489420565879163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26530912907319227421172217 19898184680489420565879163)
        ·
          refine ⟨29847277020734130848818745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19898184680489420565879163 29847277020734130848818745)
          ·
            refine ⟨22385457765550598136614059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29847277020734130848818745 22385457765550598136614059)
            ·
              refine ⟨33578186648325897204921089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22385457765550598136614059 33578186648325897204921089)
              ·
                refine ⟨25183639986244422903690817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33578186648325897204921089 25183639986244422903690817)
                ·
                  refine ⟨18887729989683317177768113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25183639986244422903690817 18887729989683317177768113)
                  ·
                    refine ⟨14165797492262487883326085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18887729989683317177768113 14165797492262487883326085)
                    ·
                      refine ⟨2656087029799216478123641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14165797492262487883326085 2656087029799216478123641)
                      ·
                        rfl

theorem cell23_5172711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_5172711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172711 prefixEnd_5172711 := by exact prefixLift 5172711
  have htrace : WordTrace (prefixWord ++ tailWord_5172711) baseStart_5172711 baseEnd_5172711 := by
    simpa [prefixWord, tailWord_5172711, baseEnd_5172711] using wordTrace_append hprefix tailTrace_5172711
  have hstable : (prefixWord ++ tailWord_5172711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172711).length < 2 ^ (prefixWord ++ tailWord_5172711).sum := by decide
  have hdescent : baseEnd_5172711 < baseStart_5172711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172721 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 7]
def baseStart_5172721 : Nat := 118140960795 + 5172721 * 2 ^ 59
def prefixEnd_5172721 : Nat := 4983230072969 + 3 ^ 40 * 5172721 * 2
def baseEnd_5172721 : Nat := 295121351622862382110955

theorem tailTrace_5172721 : CollatzResearch.WordTrace tailWord_5172721 prefixEnd_5172721 295121351622862382110955 := by
  unfold tailWord_5172721
  simp only [CollatzResearch.WordTrace]
  refine ⟨188664634293122722258422017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125776422862081814838948011 188664634293122722258422017)
  ·
    refine ⟨141498475719842041693816513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188664634293122722258422017 141498475719842041693816513)
    ·
      refine ⟨106123856789881531270362385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141498475719842041693816513 106123856789881531270362385)
      ·
        refine ⟨79592892592411148452771789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106123856789881531270362385 79592892592411148452771789)
        ·
          refine ⟨29847334722154180669789421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79592892592411148452771789 29847334722154180669789421)
          ·
            refine ⟨11192750520807817751171033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29847334722154180669789421 11192750520807817751171033)
            ·
              refine ⟨8394562890605863313378275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11192750520807817751171033 8394562890605863313378275)
              ·
                refine ⟨12591844335908794970067413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8394562890605863313378275 12591844335908794970067413)
                ·
                  refine ⟨295121351622862382110955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12591844335908794970067413 295121351622862382110955)
                  ·
                    rfl

theorem cell23_5172721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 7].length) (baseStart_5172721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172721 prefixEnd_5172721 := by exact prefixLift 5172721
  have htrace : WordTrace (prefixWord ++ tailWord_5172721) baseStart_5172721 baseEnd_5172721 := by
    simpa [prefixWord, tailWord_5172721, baseEnd_5172721] using wordTrace_append hprefix tailTrace_5172721
  have hstable : (prefixWord ++ tailWord_5172721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172721).length < 2 ^ (prefixWord ++ tailWord_5172721).sum := by decide
  have hdescent : baseEnd_5172721 < baseStart_5172721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172738 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 7]
def baseStart_5172738 : Nat := 118140960795 + 5172738 * 2 ^ 59
def prefixEnd_5172738 : Nat := 4983230072969 + 3 ^ 40 * 5172738 * 2
def baseEnd_5172738 : Nat := 295122321530765319165113

theorem tailTrace_5172738 : CollatzResearch.WordTrace tailWord_5172738 prefixEnd_5172738 295122321530765319165113 := by
  unfold tailWord_5172738
  simp only [CollatzResearch.WordTrace]
  refine ⟨47166313583515283540447717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125776836222707422774527245 47166313583515283540447717)
  ·
    refine ⟨8843683796909115663833947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47166313583515283540447717 8843683796909115663833947)
    ·
      refine ⟨13265525695363673495750921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8843683796909115663833947 13265525695363673495750921)
      ·
        refine ⟨9949144271522755121813191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13265525695363673495750921 9949144271522755121813191)
        ·
          refine ⟨14923716407284132682719787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9949144271522755121813191 14923716407284132682719787)
          ·
            refine ⟨22385574610926199024079681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14923716407284132682719787 22385574610926199024079681)
            ·
              refine ⟨16789180958194649268059761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22385574610926199024079681 16789180958194649268059761)
              ·
                refine ⟨12591885718645986951044821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16789180958194649268059761 12591885718645986951044821)
                ·
                  refine ⟨295122321530765319165113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12591885718645986951044821 295122321530765319165113)
                  ·
                    rfl

theorem cell23_5172738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_5172738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172738 prefixEnd_5172738 := by exact prefixLift 5172738
  have htrace : WordTrace (prefixWord ++ tailWord_5172738) baseStart_5172738 baseEnd_5172738 := by
    simpa [prefixWord, tailWord_5172738, baseEnd_5172738] using wordTrace_append hprefix tailTrace_5172738
  have hstable : (prefixWord ++ tailWord_5172738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172738).length < 2 ^ (prefixWord ++ tailWord_5172738).sum := by decide
  have hdescent : baseEnd_5172738 < baseStart_5172738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172768 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 2, 5]
def baseStart_5172768 : Nat := 118140960795 + 5172768 * 2 ^ 59
def prefixEnd_5172768 : Nat := 4983230072969 + 3 ^ 40 * 5172768 * 2
def baseEnd_5172768 : Nat := 885372099398840918370293

theorem tailTrace_5172768 : CollatzResearch.WordTrace tailWord_5172768 prefixEnd_5172768 885372099398840918370293 := by
  unfold tailWord_5172768
  simp only [CollatzResearch.WordTrace]
  refine ⟨94333174261976224642691479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125777565682634966190255305 94333174261976224642691479)
  ·
    refine ⟨141499761392964336964037219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94333174261976224642691479 141499761392964336964037219)
    ·
      refine ⟨212249642089446505446055829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141499761392964336964037219 212249642089446505446055829)
      ·
        refine ⟨9949201972942804942783867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 212249642089446505446055829 9949201972942804942783867)
        ·
          refine ⟨14923802959414207414175801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9949201972942804942783867 14923802959414207414175801)
          ·
            refine ⟨11192852219560655560631851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14923802959414207414175801 11192852219560655560631851)
            ·
              refine ⟨16789278329340983340947777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11192852219560655560631851 16789278329340983340947777)
              ·
                refine ⟨12591958747005737505710833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16789278329340983340947777 12591958747005737505710833)
                ·
                  refine ⟨9443969060254303129283125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12591958747005737505710833 9443969060254303129283125)
                  ·
                    refine ⟨885372099398840918370293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9443969060254303129283125 885372099398840918370293)
                    ·
                      rfl

theorem cell23_5172768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 5].length) (baseStart_5172768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172768 prefixEnd_5172768 := by exact prefixLift 5172768
  have htrace : WordTrace (prefixWord ++ tailWord_5172768) baseStart_5172768 baseEnd_5172768 := by
    simpa [prefixWord, tailWord_5172768, baseEnd_5172768] using wordTrace_append hprefix tailTrace_5172768
  have hstable : (prefixWord ++ tailWord_5172768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172768).length < 2 ^ (prefixWord ++ tailWord_5172768).sum := by decide
  have hdescent : baseEnd_5172768 < baseStart_5172768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172828 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 6]
def baseStart_5172828 : Nat := 118140960795 + 5172828 * 2 ^ 59
def prefixEnd_5172828 : Nat := 4983230072969 + 3 ^ 40 * 5172828 * 2
def baseEnd_5172828 : Nat := 295127456337310280040067

theorem tailTrace_5172828 : CollatzResearch.WordTrace tailWord_5172828 prefixEnd_5172828 295127456337310280040067 := by
  unfold tailWord_5172828
  simp only [CollatzResearch.WordTrace]
  refine ⟨94334268451867539766283569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125779024602490053021711425 94334268451867539766283569)
  ·
    refine ⟨70750701338900654824712677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94334268451867539766283569 70750701338900654824712677)
    ·
      refine ⟨13265756501043872779633627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70750701338900654824712677 13265756501043872779633627)
      ·
        refine ⟨19898634751565809169450441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13265756501043872779633627 19898634751565809169450441)
        ·
          refine ⟨14923976063674356877087831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19898634751565809169450441 14923976063674356877087831)
          ·
            refine ⟨22385964095511535315631747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14923976063674356877087831 22385964095511535315631747)
            ·
              refine ⟨33578946143267302973447621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22385964095511535315631747 33578946143267302973447621)
              ·
                refine ⟨6296052401862619307521429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33578946143267302973447621 6296052401862619307521429)
                ·
                  refine ⟨295127456337310280040067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6296052401862619307521429 295127456337310280040067)
                  ·
                    rfl

theorem cell23_5172828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 6].length) (baseStart_5172828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172828 prefixEnd_5172828 := by exact prefixLift 5172828
  have htrace : WordTrace (prefixWord ++ tailWord_5172828) baseStart_5172828 baseEnd_5172828 := by
    simpa [prefixWord, tailWord_5172828, baseEnd_5172828] using wordTrace_append hprefix tailTrace_5172828
  have hstable : (prefixWord ++ tailWord_5172828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172828).length < 2 ^ (prefixWord ++ tailWord_5172828).sum := by decide
  have hdescent : baseEnd_5172828 < baseStart_5172828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172841 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 3, 5]
def baseStart_5172841 : Nat := 118140960795 + 5172841 * 2 ^ 59
def prefixEnd_5172841 : Nat := 4983230072969 + 3 ^ 40 * 5172841 * 2
def baseEnd_5172841 : Nat := 885384594094766989832681

theorem tailTrace_5172841 : CollatzResearch.WordTrace tailWord_5172841 prefixEnd_5172841 885384594094766989832681 := by
  unfold tailWord_5172841
  simp only [CollatzResearch.WordTrace]
  refine ⟨188669011052687982752790377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125779340701791988501860251 188669011052687982752790377)
  ·
    refine ⟨141501758289515987064592783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188669011052687982752790377 141501758289515987064592783)
    ·
      refine ⟨212252637434273980596889175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141501758289515987064592783 212252637434273980596889175)
      ·
        refine ⟨318378956151410970895333763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212252637434273980596889175 318378956151410970895333763)
        ·
          refine ⟨477568434227116456343000645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318378956151410970895333763 477568434227116456343000645)
          ·
            refine ⟨89544081417584335564312621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 477568434227116456343000645 89544081417584335564312621)
            ·
              refine ⟨33579030531594125836617233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89544081417584335564312621 33579030531594125836617233)
              ·
                refine ⟨25184272898695594377462925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33579030531594125836617233 25184272898695594377462925)
                ·
                  refine ⟨9444102337010847891548597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25184272898695594377462925 9444102337010847891548597)
                  ·
                    refine ⟨885384594094766989832681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9444102337010847891548597 885384594094766989832681)
                    ·
                      rfl

theorem cell23_5172841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 5].length) (baseStart_5172841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172841 prefixEnd_5172841 := by exact prefixLift 5172841
  have htrace : WordTrace (prefixWord ++ tailWord_5172841) baseStart_5172841 baseEnd_5172841 := by
    simpa [prefixWord, tailWord_5172841, baseEnd_5172841] using wordTrace_append hprefix tailTrace_5172841
  have hstable : (prefixWord ++ tailWord_5172841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172841).length < 2 ^ (prefixWord ++ tailWord_5172841).sum := by decide
  have hdescent : baseEnd_5172841 < baseStart_5172841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172865 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_5172865 : Nat := 118140960795 + 5172865 * 2 ^ 59
def prefixEnd_5172865 : Nat := 4983230072969 + 3 ^ 40 * 5172865 * 2
def baseEnd_5172865 : Nat := 2656166105820008875597933

theorem tailTrace_5172865 : CollatzResearch.WordTrace tailWord_5172865 prefixEnd_5172865 2656166105820008875597933 := by
  unfold tailWord_5172865
  simp only [CollatzResearch.WordTrace]
  refine ⟨188669886404601034851664049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125779924269734023234442699 188669886404601034851664049)
  ·
    refine ⟨141502414803450776138748037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188669886404601034851664049 141502414803450776138748037)
    ·
      refine ⟨26531702775647020526015257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141502414803450776138748037 26531702775647020526015257)
      ·
        refine ⟨19898777081735265394511443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26531702775647020526015257 19898777081735265394511443)
        ·
          refine ⟨29848165622602898091767165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19898777081735265394511443 29848165622602898091767165)
          ·
            refine ⟨11193062108476086784412687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29848165622602898091767165 11193062108476086784412687)
            ·
              refine ⟨16789593162714130176619031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11193062108476086784412687 16789593162714130176619031)
              ·
                refine ⟨25184389744071195264928547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16789593162714130176619031 25184389744071195264928547)
                ·
                  refine ⟨37776584616106792897392821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25184389744071195264928547 37776584616106792897392821)
                  ·
                    refine ⟨3541554807760011834130577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37776584616106792897392821 3541554807760011834130577)
                    ·
                      refine ⟨2656166105820008875597933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541554807760011834130577 2656166105820008875597933)
                      ·
                        rfl

theorem cell23_5172865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_5172865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172865 prefixEnd_5172865 := by exact prefixLift 5172865
  have htrace : WordTrace (prefixWord ++ tailWord_5172865) baseStart_5172865 baseEnd_5172865 := by
    simpa [prefixWord, tailWord_5172865, baseEnd_5172865] using wordTrace_append hprefix tailTrace_5172865
  have hstable : (prefixWord ++ tailWord_5172865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172865).length < 2 ^ (prefixWord ++ tailWord_5172865).sum := by decide
  have hdescent : baseEnd_5172865 < baseStart_5172865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172915 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 3]
def baseStart_5172915 : Nat := 118140960795 + 5172915 * 2 ^ 59
def prefixEnd_5172915 : Nat := 4983230072969 + 3 ^ 40 * 5172915 * 2
def baseEnd_5172915 : Nat := 2656191779852733679972703

theorem tailTrace_5172915 : CollatzResearch.WordTrace tailWord_5172915 prefixEnd_5172915 2656191779852733679972703 := by
  unfold tailWord_5172915
  simp only [CollatzResearch.WordTrace]
  refine ⟨188671710054419893390984199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125781140036279928927322799 188671710054419893390984199)
  ·
    refine ⟨283007565081629840086476299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188671710054419893390984199 283007565081629840086476299)
    ·
      refine ⟨424511347622444760129714449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283007565081629840086476299 424511347622444760129714449)
      ·
        refine ⟨318383510716833570097285837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424511347622444760129714449 318383510716833570097285837)
        ·
          refine ⟨119393816518812588786482189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318383510716833570097285837 119393816518812588786482189)
          ·
            refine ⟨44772681194554720794930821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119393816518812588786482189 44772681194554720794930821)
            ·
              refine ⟨8394877723979010149049529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44772681194554720794930821 8394877723979010149049529)
              ·
                refine ⟨6296158292984257611787147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8394877723979010149049529 6296158292984257611787147)
                ·
                  refine ⟨9444237439476386417680721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296158292984257611787147 9444237439476386417680721)
                  ·
                    refine ⟨7083178079607289813260541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9444237439476386417680721 7083178079607289813260541)
                    ·
                      refine ⟨2656191779852733679972703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7083178079607289813260541 2656191779852733679972703)
                      ·
                        rfl

theorem cell23_5172915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 1, 2, 3].length) (baseStart_5172915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172915 prefixEnd_5172915 := by exact prefixLift 5172915
  have htrace : WordTrace (prefixWord ++ tailWord_5172915) baseStart_5172915 baseEnd_5172915 := by
    simpa [prefixWord, tailWord_5172915, baseEnd_5172915] using wordTrace_append hprefix tailTrace_5172915
  have hstable : (prefixWord ++ tailWord_5172915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172915).length < 2 ^ (prefixWord ++ tailWord_5172915).sum := by decide
  have hdescent : baseEnd_5172915 < baseStart_5172915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172928 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 3]
def baseStart_5172928 : Nat := 118140960795 + 5172928 * 2 ^ 59
def prefixEnd_5172928 : Nat := 4983230072969 + 3 ^ 40 * 5172928 * 2
def baseEnd_5172928 : Nat := 2656198455101242129110143

theorem tailTrace_5172928 : CollatzResearch.WordTrace tailWord_5172928 prefixEnd_5172928 2656198455101242129110143 := by
  unfold tailWord_5172928
  simp only [CollatzResearch.WordTrace]
  refine ⟨94336092101686398305603719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125781456135581864407471625 94336092101686398305603719)
  ·
    refine ⟨141504138152529597458405579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94336092101686398305603719 141504138152529597458405579)
    ·
      refine ⟨212256207228794396187608369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141504138152529597458405579 212256207228794396187608369)
      ·
        refine ⟨159192155421595797140706277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212256207228794396187608369 159192155421595797140706277)
        ·
          refine ⟨29848529141549211963882427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159192155421595797140706277 29848529141549211963882427)
          ·
            refine ⟨44772793712323817945823641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29848529141549211963882427 44772793712323817945823641)
            ·
              refine ⟨33579595284242863459367731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44772793712323817945823641 33579595284242863459367731)
              ·
                refine ⟨50369392926364295189051597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33579595284242863459367731 50369392926364295189051597)
                ·
                  refine ⟨18888522347386610695894349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50369392926364295189051597 18888522347386610695894349)
                  ·
                    refine ⟨7083195880269979010960381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18888522347386610695894349 7083195880269979010960381)
                    ·
                      refine ⟨2656198455101242129110143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7083195880269979010960381 2656198455101242129110143)
                      ·
                        rfl

theorem cell23_5172928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_5172928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172928 prefixEnd_5172928 := by exact prefixLift 5172928
  have htrace : WordTrace (prefixWord ++ tailWord_5172928) baseStart_5172928 baseEnd_5172928 := by
    simpa [prefixWord, tailWord_5172928, baseEnd_5172928] using wordTrace_append hprefix tailTrace_5172928
  have hstable : (prefixWord ++ tailWord_5172928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172928).length < 2 ^ (prefixWord ++ tailWord_5172928).sum := by decide
  have hdescent : baseEnd_5172928 < baseStart_5172928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172945 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 3]
def baseStart_5172945 : Nat := 118140960795 + 5172945 * 2 ^ 59
def prefixEnd_5172945 : Nat := 4983230072969 + 3 ^ 40 * 5172945 * 2
def baseEnd_5172945 : Nat := 2656207184272368562597565

theorem tailTrace_5172945 : CollatzResearch.WordTrace tailWord_5172945 prefixEnd_5172945 2656207184272368562597565 := by
  unfold tailWord_5172945
  simp only [CollatzResearch.WordTrace]
  refine ⟨188672804244311208514576289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125781869496207472343050859 188672804244311208514576289)
  ·
    refine ⟨141504603183233406385932217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188672804244311208514576289 141504603183233406385932217)
    ·
      refine ⟨106128452387425054789449163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141504603183233406385932217 106128452387425054789449163)
      ·
        refine ⟨159192678581137582184173745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106128452387425054789449163 159192678581137582184173745)
        ·
          refine ⟨119394508935853186638130309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159192678581137582184173745 119394508935853186638130309)
          ·
            refine ⟨22386470425472472494649433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119394508935853186638130309 22386470425472472494649433)
            ·
              refine ⟨16789852819104354370987075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22386470425472472494649433 16789852819104354370987075)
              ·
                refine ⟨25184779228656531556480613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16789852819104354370987075 25184779228656531556480613)
                ·
                  refine ⟨4722146105373099666840115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25184779228656531556480613 4722146105373099666840115)
                  ·
                    refine ⟨7083219158059649500260173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4722146105373099666840115 7083219158059649500260173)
                    ·
                      refine ⟨2656207184272368562597565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7083219158059649500260173 2656207184272368562597565)
                      ·
                        rfl

theorem cell23_5172945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_5172945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172945 prefixEnd_5172945 := by exact prefixLift 5172945
  have htrace : WordTrace (prefixWord ++ tailWord_5172945) baseStart_5172945 baseEnd_5172945 := by
    simpa [prefixWord, tailWord_5172945, baseEnd_5172945] using wordTrace_append hprefix tailTrace_5172945
  have hstable : (prefixWord ++ tailWord_5172945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172945).length < 2 ^ (prefixWord ++ tailWord_5172945).sum := by decide
  have hdescent : baseEnd_5172945 < baseStart_5172945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172956 : List Nat := [2, 2, 5, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5172956 : Nat := 118140960795 + 5172956 * 2 ^ 59
def prefixEnd_5172956 : Nat := 4983230072969 + 3 ^ 40 * 5172956 * 2
def baseEnd_5172956 : Nat := 885404277519856006520005

theorem tailTrace_5172956 : CollatzResearch.WordTrace tailWord_5172956 prefixEnd_5172956 885404277519856006520005 := by
  unfold tailWord_5172956
  simp only [CollatzResearch.WordTrace]
  refine ⟨94336602723635678696613361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125782136964847571595484481 94336602723635678696613361)
  ·
    refine ⟨70752452042726759022460021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94336602723635678696613361 70752452042726759022460021)
    ·
      refine ⟨6633042379005633658355627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70752452042726759022460021 6633042379005633658355627)
      ·
        refine ⟨9949563568508450487533441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6633042379005633658355627 9949563568508450487533441)
        ·
          refine ⟨7462172676381337865650081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9949563568508450487533441 7462172676381337865650081)
          ·
            refine ⟨5596629507286003399237561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7462172676381337865650081 5596629507286003399237561)
            ·
              refine ⟨4197472130464502549428171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5596629507286003399237561 4197472130464502549428171)
              ·
                refine ⟨6296208195696753824142257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4197472130464502549428171 6296208195696753824142257)
                ·
                  refine ⟨4722156146772565368106693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6296208195696753824142257 4722156146772565368106693)
                  ·
                    refine ⟨885404277519856006520005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4722156146772565368106693 885404277519856006520005)
                    ·
                      rfl

theorem cell23_5172956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5172956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172956 prefixEnd_5172956 := by exact prefixLift 5172956
  have htrace : WordTrace (prefixWord ++ tailWord_5172956) baseStart_5172956 baseEnd_5172956 := by
    simpa [prefixWord, tailWord_5172956, baseEnd_5172956] using wordTrace_append hprefix tailTrace_5172956
  have hstable : (prefixWord ++ tailWord_5172956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172956).length < 2 ^ (prefixWord ++ tailWord_5172956).sum := by decide
  have hdescent : baseEnd_5172956 < baseStart_5172956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172972 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 1, 3, 2]
def baseStart_5172972 : Nat := 118140960795 + 5172972 * 2 ^ 59
def prefixEnd_5172972 : Nat := 4983230072969 + 3 ^ 40 * 5172972 * 2
def baseEnd_5172972 : Nat := 2656221048250039956959941

theorem tailTrace_5172972 : CollatzResearch.WordTrace tailWord_5172972 prefixEnd_5172972 2656221048250039956959941 := by
  unfold tailWord_5172972
  simp only [CollatzResearch.WordTrace]
  refine ⟨94336894507606696062904585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125782526010142261417206113 94336894507606696062904585)
  ·
    refine ⟨70752670880705022047178439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94336894507606696062904585 70752670880705022047178439)
    ·
      refine ⟨106129006321057533070767659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70752670880705022047178439 106129006321057533070767659)
      ·
        refine ⟨159193509481586299606151489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106129006321057533070767659 159193509481586299606151489)
        ·
          refine ⟨119395132111189724704613617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159193509481586299606151489 119395132111189724704613617)
          ·
            refine ⟨89546349083392293528460213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119395132111189724704613617 89546349083392293528460213)
            ·
              refine ⟨8394970226568027518293145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89546349083392293528460213 8394970226568027518293145)
              ·
                refine ⟨6296227669926020638719859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8394970226568027518293145 6296227669926020638719859)
                ·
                  refine ⟨9444341504889030958079789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296227669926020638719859 9444341504889030958079789)
                  ·
                    refine ⟨3541628064333386609279921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9444341504889030958079789 3541628064333386609279921)
                    ·
                      refine ⟨2656221048250039956959941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541628064333386609279921 2656221048250039956959941)
                      ·
                        rfl

theorem cell23_5172972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_5172972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172972 prefixEnd_5172972 := by exact prefixLift 5172972
  have htrace : WordTrace (prefixWord ++ tailWord_5172972) baseStart_5172972 baseEnd_5172972 := by
    simpa [prefixWord, tailWord_5172972, baseEnd_5172972] using wordTrace_append hprefix tailTrace_5172972
  have hstable : (prefixWord ++ tailWord_5172972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172972).length < 2 ^ (prefixWord ++ tailWord_5172972).sum := by decide
  have hdescent : baseEnd_5172972 < baseStart_5172972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5172988 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_5172988 : Nat := 118140960795 + 5172988 * 2 ^ 59
def prefixEnd_5172988 : Nat := 4983230072969 + 3 ^ 40 * 5172988 * 2
def baseEnd_5172988 : Nat := 2656229263940511894359867

theorem tailTrace_5172988 : CollatzResearch.WordTrace tailWord_5172988 prefixEnd_5172988 2656229263940511894359867 := by
  unfold tailWord_5172988
  simp only [CollatzResearch.WordTrace]
  refine ⟨94337186291577713429195809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125782915055436951238927745 94337186291577713429195809)
  ·
    refine ⟨70752889718683285071896857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94337186291577713429195809 70752889718683285071896857)
    ·
      refine ⟨53064667289012463803922643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70752889718683285071896857 53064667289012463803922643)
      ·
        refine ⟨79597000933518695705883965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53064667289012463803922643 79597000933518695705883965)
        ·
          refine ⟨29848875350069510889706487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79597000933518695705883965 29848875350069510889706487)
          ·
            refine ⟨44773313025104266334559731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29848875350069510889706487 44773313025104266334559731)
            ·
              refine ⟨67159969537656399501839597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44773313025104266334559731 67159969537656399501839597)
              ·
                refine ⟨25184988576621149813189849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67159969537656399501839597 25184988576621149813189849)
                ·
                  refine ⟨18888741432465862359892387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25184988576621149813189849 18888741432465862359892387)
                  ·
                    refine ⟨28333112148698793539838581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18888741432465862359892387 28333112148698793539838581)
                    ·
                      refine ⟨2656229263940511894359867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28333112148698793539838581 2656229263940511894359867)
                      ·
                        rfl

theorem cell23_5172988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_5172988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5172988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5172988 prefixEnd_5172988 := by exact prefixLift 5172988
  have htrace : WordTrace (prefixWord ++ tailWord_5172988) baseStart_5172988 baseEnd_5172988 := by
    simpa [prefixWord, tailWord_5172988, baseEnd_5172988] using wordTrace_append hprefix tailTrace_5172988
  have hstable : (prefixWord ++ tailWord_5172988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5172988).length < 2 ^ (prefixWord ++ tailWord_5172988).sum := by decide
  have hdescent : baseEnd_5172988 < baseStart_5172988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5172988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173015 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5173015 : Nat := 118140960795 + 5173015 * 2 ^ 59
def prefixEnd_5173015 : Nat := 4983230072969 + 3 ^ 40 * 5173015 * 2
def baseEnd_5173015 : Nat := 2656243127918183288722243

theorem tailTrace_5173015 : CollatzResearch.WordTrace tailWord_5173015 prefixEnd_5173015 2656243127918183288722243 := by
  unfold tailWord_5173015
  simp only [CollatzResearch.WordTrace]
  refine ⟨188675357354057610469624499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125783571569371740313082999 188675357354057610469624499)
  ·
    refine ⟨283013036031086415704436749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188675357354057610469624499 283013036031086415704436749)
    ·
      refine ⟨106129888511657405889163781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283013036031086415704436749 106129888511657405889163781)
      ·
        refine ⟨19899354095935763604218209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106129888511657405889163781 19899354095935763604218209)
        ·
          refine ⟨14924515571951822703163657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19899354095935763604218209 14924515571951822703163657)
          ·
            refine ⟨11193386678963867027372743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14924515571951822703163657 11193386678963867027372743)
            ·
              refine ⟨16790080018445800541059115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11193386678963867027372743 16790080018445800541059115)
              ·
                refine ⟨25185120027668700811588673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16790080018445800541059115 25185120027668700811588673)
                ·
                  refine ⟨18888840020751525608691505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25185120027668700811588673 18888840020751525608691505)
                  ·
                    refine ⟨14166630015563644206518629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18888840020751525608691505 14166630015563644206518629)
                    ·
                      refine ⟨2656243127918183288722243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14166630015563644206518629 2656243127918183288722243)
                      ·
                        rfl

theorem cell23_5173015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5173015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173015 prefixEnd_5173015 := by exact prefixLift 5173015
  have htrace : WordTrace (prefixWord ++ tailWord_5173015) baseStart_5173015 baseEnd_5173015 := by
    simpa [prefixWord, tailWord_5173015, baseEnd_5173015] using wordTrace_append hprefix tailTrace_5173015
  have hstable : (prefixWord ++ tailWord_5173015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173015).length < 2 ^ (prefixWord ++ tailWord_5173015).sum := by decide
  have hdescent : baseEnd_5173015 < baseStart_5173015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173042 : List Nat := [3, 2, 1, 1, 3, 3, 2, 3, 5]
def baseStart_5173042 : Nat := 118140960795 + 5173042 * 2 ^ 59
def prefixEnd_5173042 : Nat := 4983230072969 + 3 ^ 40 * 5173042 * 2
def baseEnd_5173042 : Nat := 295139665766206075898291

theorem tailTrace_5173042 : CollatzResearch.WordTrace tailWord_5173042 prefixEnd_5173042 295139665766206075898291 := by
  unfold tailWord_5173042
  simp only [CollatzResearch.WordTrace]
  refine ⟨47169085531239948520214345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125784228083306529387238253 47169085531239948520214345)
  ·
    refine ⟨35376814148429961390160759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47169085531239948520214345 35376814148429961390160759)
    ·
      refine ⟨53065221222644942085241139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35376814148429961390160759 53065221222644942085241139)
      ·
        refine ⟨79597831833967413127861709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53065221222644942085241139 79597831833967413127861709)
        ·
          refine ⟨29849186937737779922948141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79597831833967413127861709 29849186937737779922948141)
          ·
            refine ⟨11193445101651667471105553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29849186937737779922948141 11193445101651667471105553)
            ·
              refine ⟨8395083826238750603329165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11193445101651667471105553 8395083826238750603329165)
              ·
                refine ⟨3148156434839531476248437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8395083826238750603329165 3148156434839531476248437)
                ·
                  refine ⟨295139665766206075898291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3148156434839531476248437 295139665766206075898291)
                  ·
                    rfl

theorem cell23_5173042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_5173042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173042 prefixEnd_5173042 := by exact prefixLift 5173042
  have htrace : WordTrace (prefixWord ++ tailWord_5173042) baseStart_5173042 baseEnd_5173042 := by
    simpa [prefixWord, tailWord_5173042, baseEnd_5173042] using wordTrace_append hprefix tailTrace_5173042
  have hstable : (prefixWord ++ tailWord_5173042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173042).length < 2 ^ (prefixWord ++ tailWord_5173042).sum := by decide
  have hdescent : baseEnd_5173042 < baseStart_5173042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173095 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_5173095 : Nat := 118140960795 + 5173095 * 2 ^ 59
def prefixEnd_5173095 : Nat := 4983230072969 + 3 ^ 40 * 5173095 * 2
def baseEnd_5173095 : Nat := 2656284206370542975721875

theorem tailTrace_5173095 : CollatzResearch.WordTrace tailWord_5173095 prefixEnd_5173095 2656284206370542975721875 := by
  unfold tailWord_5173095
  simp only [CollatzResearch.WordTrace]
  refine ⟨188678275193767784132536739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125785516795845189421691159 188678275193767784132536739)
  ·
    refine ⟨283017412790651676198805109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188678275193767784132536739 283017412790651676198805109)
    ·
      refine ⟨26532882449123594643637979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 283017412790651676198805109 26532882449123594643637979)
      ·
        refine ⟨39799323673685391965456969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26532882449123594643637979 39799323673685391965456969)
        ·
          refine ⟨29849492755264043974092727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39799323673685391965456969 29849492755264043974092727)
          ·
            refine ⟨44774239132896065961139091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29849492755264043974092727 44774239132896065961139091)
            ·
              refine ⟨67161358699344098941708637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44774239132896065961139091 67161358699344098941708637)
              ·
                refine ⟨25185509512254037103140739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67161358699344098941708637 25185509512254037103140739)
                ·
                  refine ⟨37778264268381055654711109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25185509512254037103140739 37778264268381055654711109)
                  ·
                    refine ⟨7083424550321447935258333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37778264268381055654711109 7083424550321447935258333)
                    ·
                      refine ⟨2656284206370542975721875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7083424550321447935258333 2656284206370542975721875)
                      ·
                        rfl

theorem cell23_5173095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_5173095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173095 prefixEnd_5173095 := by exact prefixLift 5173095
  have htrace : WordTrace (prefixWord ++ tailWord_5173095) baseStart_5173095 baseEnd_5173095 := by
    simpa [prefixWord, tailWord_5173095, baseEnd_5173095] using wordTrace_append hprefix tailTrace_5173095
  have hstable : (prefixWord ++ tailWord_5173095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173095).length < 2 ^ (prefixWord ++ tailWord_5173095).sum := by decide
  have hdescent : baseEnd_5173095 < baseStart_5173095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173169 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 2, 3, 2]
def baseStart_5173169 : Nat := 118140960795 + 5173169 * 2 ^ 59
def prefixEnd_5173169 : Nat := 4983230072969 + 3 ^ 40 * 5173169 * 2
def baseEnd_5173169 : Nat := 2656322203938975686196535

theorem tailTrace_5173169 : CollatzResearch.WordTrace tailWord_5173169 prefixEnd_5173169 2656322203938975686196535 := by
  unfold tailWord_5173169
  simp only [CollatzResearch.WordTrace]
  refine ⟨188680974195499694770730561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125787316130333129847153707 188680974195499694770730561)
  ·
    refine ⟨141510730646624771078047921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188680974195499694770730561 141510730646624771078047921)
    ·
      refine ⟨106133047984968578308535941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141510730646624771078047921 106133047984968578308535941)
      ·
        refine ⟨19899946497181608432850489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106133047984968578308535941 19899946497181608432850489)
        ·
          refine ⟨14924959872886206324637867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19899946497181608432850489 14924959872886206324637867)
          ·
            refine ⟨22387439809329309486956801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14924959872886206324637867 22387439809329309486956801)
            ·
              refine ⟨16790579856996982115217601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22387439809329309486956801 16790579856996982115217601)
              ·
                refine ⟨12592934892747736586413201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16790579856996982115217601 12592934892747736586413201)
                ·
                  refine ⟨9444701169560802439809901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12592934892747736586413201 9444701169560802439809901)
                  ·
                    refine ⟨3541762938585300914928713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9444701169560802439809901 3541762938585300914928713)
                    ·
                      refine ⟨2656322203938975686196535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541762938585300914928713 2656322203938975686196535)
                      ·
                        rfl

theorem cell23_5173169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_5173169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173169 prefixEnd_5173169 := by exact prefixLift 5173169
  have htrace : WordTrace (prefixWord ++ tailWord_5173169) baseStart_5173169 baseEnd_5173169 := by
    simpa [prefixWord, tailWord_5173169, baseEnd_5173169] using wordTrace_append hprefix tailTrace_5173169
  have hstable : (prefixWord ++ tailWord_5173169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173169).length < 2 ^ (prefixWord ++ tailWord_5173169).sum := by decide
  have hdescent : baseEnd_5173169 < baseStart_5173169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173182 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_5173182 : Nat := 118140960795 + 5173182 * 2 ^ 59
def prefixEnd_5173182 : Nat := 4983230072969 + 3 ^ 40 * 5173182 * 2
def baseEnd_5173182 : Nat := 2656328879187484135333975

theorem tailTrace_5173182 : CollatzResearch.WordTrace tailWord_5173182 prefixEnd_5173182 2656328879187484135333975 := by
  unfold tailWord_5173182
  simp only [CollatzResearch.WordTrace]
  refine ⟨23585181043056574748869225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125787632229635065327302533 23585181043056574748869225)
  ·
    refine ⟨17688885782292431061651919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23585181043056574748869225 17688885782292431061651919)
    ·
      refine ⟨26533328673438646592477879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17688885782292431061651919 26533328673438646592477879)
      ·
        refine ⟨39799993010157969888716819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26533328673438646592477879 39799993010157969888716819)
        ·
          refine ⟨59699989515236954833075229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39799993010157969888716819 59699989515236954833075229)
          ·
            refine ⟨22387496068213858062403211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59699989515236954833075229 22387496068213858062403211)
            ·
              refine ⟨33581244102320787093604817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22387496068213858062403211 33581244102320787093604817)
              ·
                refine ⟨25185933076740590320203613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33581244102320787093604817 25185933076740590320203613)
                ·
                  refine ⟨9444724903777721370076355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25185933076740590320203613 9444724903777721370076355)
                  ·
                    refine ⟨14167087355666582055114533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9444724903777721370076355 14167087355666582055114533)
                    ·
                      refine ⟨2656328879187484135333975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14167087355666582055114533 2656328879187484135333975)
                      ·
                        rfl

theorem cell23_5173182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_5173182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173182 prefixEnd_5173182 := by exact prefixLift 5173182
  have htrace : WordTrace (prefixWord ++ tailWord_5173182) baseStart_5173182 baseEnd_5173182 := by
    simpa [prefixWord, tailWord_5173182, baseEnd_5173182] using wordTrace_append hprefix tailTrace_5173182
  have hstable : (prefixWord ++ tailWord_5173182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173182).length < 2 ^ (prefixWord ++ tailWord_5173182).sum := by decide
  have hdescent : baseEnd_5173182 < baseStart_5173182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173192 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 1, 6]
def baseStart_5173192 : Nat := 118140960795 + 5173192 * 2 ^ 59
def prefixEnd_5173192 : Nat := 4983230072969 + 3 ^ 40 * 5173192 * 2
def baseEnd_5173192 : Nat := 885444671331343032069643

theorem tailTrace_5173192 : CollatzResearch.WordTrace tailWord_5173192 prefixEnd_5173192 885444671331343032069643 := by
  unfold tailWord_5173192
  simp only [CollatzResearch.WordTrace]
  refine ⟨94340906537208184849408915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125787875382944246465878553 94340906537208184849408915)
  ·
    refine ⟨141511359805812277274113373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94340906537208184849408915 141511359805812277274113373)
    ·
      refine ⟨53066759927179603977792515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141511359805812277274113373 53066759927179603977792515)
      ·
        refine ⟨79600139890769405966688773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53066759927179603977792515 79600139890769405966688773)
        ·
          refine ⟨14925026229519263618754145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79600139890769405966688773 14925026229519263618754145)
          ·
            refine ⟨11193769672139447714065609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14925026229519263618754145 11193769672139447714065609)
            ·
              refine ⟨8395327254104585785549207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11193769672139447714065609 8395327254104585785549207)
              ·
                refine ⟨12592990881156878678323811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8395327254104585785549207 12592990881156878678323811)
                ·
                  refine ⟨18889486321735318017485717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12592990881156878678323811 18889486321735318017485717)
                  ·
                    refine ⟨885444671331343032069643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18889486321735318017485717 885444671331343032069643)
                    ·
                      rfl

theorem cell23_5173192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_5173192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173192 prefixEnd_5173192 := by exact prefixLift 5173192
  have htrace : WordTrace (prefixWord ++ tailWord_5173192) baseStart_5173192 baseEnd_5173192 := by
    simpa [prefixWord, tailWord_5173192, baseEnd_5173192] using wordTrace_append hprefix tailTrace_5173192
  have hstable : (prefixWord ++ tailWord_5173192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173192).length < 2 ^ (prefixWord ++ tailWord_5173192).sum := by decide
  have hdescent : baseEnd_5173192 < baseStart_5173192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173199 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 3, 2, 2]
def baseStart_5173199 : Nat := 118140960795 + 5173199 * 2 ^ 59
def prefixEnd_5173199 : Nat := 4983230072969 + 3 ^ 40 * 5173199 * 2
def baseEnd_5173199 : Nat := 2656337608358610568821397

theorem tailTrace_5173199 : CollatzResearch.WordTrace tailWord_5173199 prefixEnd_5173199 2656337608358610568821397 := by
  unfold tailWord_5173199
  simp only [CollatzResearch.WordTrace]
  refine ⟨188682068385391009894322651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125788045590260673262881767 188682068385391009894322651)
  ·
    refine ⟨283023102578086514841483977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188682068385391009894322651 283023102578086514841483977)
    ·
      refine ⟨212267326933564886131112983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283023102578086514841483977 212267326933564886131112983)
      ·
        refine ⟨318400990400347329196669475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212267326933564886131112983 318400990400347329196669475)
        ·
          refine ⟨477601485600520993795004213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318400990400347329196669475 477601485600520993795004213)
          ·
            refine ⟨44775139275048843168281645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 477601485600520993795004213 44775139275048843168281645)
            ·
              refine ⟨16790677228143316188105617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44775139275048843168281645 16790677228143316188105617)
              ·
                refine ⟨12593007921107487141079213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16790677228143316188105617 12593007921107487141079213)
                ·
                  refine ⟨4722377970415307677904705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12593007921107487141079213 4722377970415307677904705)
                  ·
                    refine ⟨3541783477811480758428529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4722377970415307677904705 3541783477811480758428529)
                    ·
                      refine ⟨2656337608358610568821397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541783477811480758428529 2656337608358610568821397)
                      ·
                        rfl

theorem cell23_5173199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 2, 2].length) (baseStart_5173199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173199 prefixEnd_5173199 := by exact prefixLift 5173199
  have htrace : WordTrace (prefixWord ++ tailWord_5173199) baseStart_5173199 baseEnd_5173199 := by
    simpa [prefixWord, tailWord_5173199, baseEnd_5173199] using wordTrace_append hprefix tailTrace_5173199
  have hstable : (prefixWord ++ tailWord_5173199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173199).length < 2 ^ (prefixWord ++ tailWord_5173199).sum := by decide
  have hdescent : baseEnd_5173199 < baseStart_5173199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173213 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_5173213 : Nat := 118140960795 + 5173213 * 2 ^ 59
def prefixEnd_5173213 : Nat := 4983230072969 + 3 ^ 40 * 5173213 * 2
def baseEnd_5173213 : Nat := 885448265695924504682111

theorem tailTrace_5173213 : CollatzResearch.WordTrace tailWord_5173213 prefixEnd_5173213 885448265695924504682111 := by
  unfold tailWord_5173213
  simp only [CollatzResearch.WordTrace]
  refine ⟨188682579007340290285332293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125788386004893526856888195 188682579007340290285332293)
  ·
    refine ⟨35377983563876304428499805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188682579007340290285332293 35377983563876304428499805)
    ·
      refine ⟨13266743836453614160687427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35377983563876304428499805 13266743836453614160687427)
      ·
        refine ⟨19900115754680421241031141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13266743836453614160687427 19900115754680421241031141)
        ·
          refine ⟨3731271704002578982693339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19900115754680421241031141 3731271704002578982693339)
          ·
            refine ⟨5596907556003868474040009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731271704002578982693339 5596907556003868474040009)
            ·
              refine ⟨4197680667002901355530007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5596907556003868474040009 4197680667002901355530007)
              ·
                refine ⟨6296521000504352033295011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4197680667002901355530007 6296521000504352033295011)
                ·
                  refine ⟨9444781500756528049942517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296521000504352033295011 9444781500756528049942517)
                  ·
                    refine ⟨885448265695924504682111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9444781500756528049942517 885448265695924504682111)
                    ·
                      rfl

theorem cell23_5173213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_5173213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173213 prefixEnd_5173213 := by exact prefixLift 5173213
  have htrace : WordTrace (prefixWord ++ tailWord_5173213) baseStart_5173213 baseEnd_5173213 := by
    simpa [prefixWord, tailWord_5173213, baseEnd_5173213] using wordTrace_append hprefix tailTrace_5173213
  have hstable : (prefixWord ++ tailWord_5173213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173213).length < 2 ^ (prefixWord ++ tailWord_5173213).sum := by decide
  have hdescent : baseEnd_5173213 < baseStart_5173213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173219 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 3]
def baseStart_5173219 : Nat := 118140960795 + 5173219 * 2 ^ 59
def prefixEnd_5173219 : Nat := 4983230072969 + 3 ^ 40 * 5173219 * 2
def baseEnd_5173219 : Nat := 2656347877971700490571305

theorem tailTrace_5173219 : CollatzResearch.WordTrace tailWord_5173219 prefixEnd_5173219 2656347877971700490571305 := by
  unfold tailWord_5173219
  simp only [CollatzResearch.WordTrace]
  refine ⟨188682797845318553310050711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125788531896879035540033807 188682797845318553310050711)
  ·
    refine ⟨283024196767977829965076067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188682797845318553310050711 283024196767977829965076067)
    ·
      refine ⟨424536295151966744947614101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283024196767977829965076067 424536295151966744947614101)
      ·
        refine ⟨19900138835248441169419411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 424536295151966744947614101 19900138835248441169419411)
        ·
          refine ⟨29850208252872661754129117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19900138835248441169419411 29850208252872661754129117)
          ·
            refine ⟨11193828094827248157798419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29850208252872661754129117 11193828094827248157798419)
            ·
              refine ⟨16790742142240872236697629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11193828094827248157798419 16790742142240872236697629)
              ·
                refine ⟨6296528303340327088761611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16790742142240872236697629 6296528303340327088761611)
                ·
                  refine ⟨9444792455010490633142417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296528303340327088761611 9444792455010490633142417)
                  ·
                    refine ⟨7083594341257867974856813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9444792455010490633142417 7083594341257867974856813)
                    ·
                      refine ⟨2656347877971700490571305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7083594341257867974856813 2656347877971700490571305)
                      ·
                        rfl

theorem cell23_5173219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_5173219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173219 prefixEnd_5173219 := by exact prefixLift 5173219
  have htrace : WordTrace (prefixWord ++ tailWord_5173219) baseStart_5173219 baseEnd_5173219 := by
    simpa [prefixWord, tailWord_5173219, baseEnd_5173219] using wordTrace_append hprefix tailTrace_5173219
  have hstable : (prefixWord ++ tailWord_5173219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173219).length < 2 ^ (prefixWord ++ tailWord_5173219).sum := by decide
  have hdescent : baseEnd_5173219 < baseStart_5173219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173246 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_5173246 : Nat := 118140960795 + 5173246 * 2 ^ 59
def prefixEnd_5173246 : Nat := 4983230072969 + 3 ^ 40 * 5173246 * 2
def baseEnd_5173246 : Nat := 2656361741949371884933681

theorem tailTrace_5173246 : CollatzResearch.WordTrace tailWord_5173246 prefixEnd_5173246 2656361741949371884933681 := by
  unfold tailWord_5173246
  simp only [CollatzResearch.WordTrace]
  refine ⟨23585472827027592115160449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125789188410813824614189061 23585472827027592115160449)
  ·
    refine ⟨17689104620270694086370337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23585472827027592115160449 17689104620270694086370337)
    ·
      refine ⟨13266828465203020564777753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17689104620270694086370337 13266828465203020564777753)
      ·
        refine ⟨9950121348902265423583315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13266828465203020564777753 9950121348902265423583315)
        ·
          refine ⟨14925182023353398135374973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9950121348902265423583315 14925182023353398135374973)
          ·
            refine ⟨5596943258757524300765615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14925182023353398135374973 5596943258757524300765615)
            ·
              refine ⟨8395414888136286451148423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5596943258757524300765615 8395414888136286451148423)
              ·
                refine ⟨12593122332204429676722635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8395414888136286451148423 12593122332204429676722635)
                ·
                  refine ⟨18889683498306644515083953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12593122332204429676722635 18889683498306644515083953)
                  ·
                    refine ⟨14167262623729983386312965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18889683498306644515083953 14167262623729983386312965)
                    ·
                      refine ⟨2656361741949371884933681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14167262623729983386312965 2656361741949371884933681)
                      ·
                        rfl

theorem cell23_5173246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_5173246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173246 prefixEnd_5173246 := by exact prefixLift 5173246
  have htrace : WordTrace (prefixWord ++ tailWord_5173246) baseStart_5173246 baseEnd_5173246 := by
    simpa [prefixWord, tailWord_5173246, baseEnd_5173246] using wordTrace_append hprefix tailTrace_5173246
  have hstable : (prefixWord ++ tailWord_5173246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173246).length < 2 ^ (prefixWord ++ tailWord_5173246).sum := by decide
  have hdescent : baseEnd_5173246 < baseStart_5173246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173276 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_5173276 : Nat := 118140960795 + 5173276 * 2 ^ 59
def prefixEnd_5173276 : Nat := 4983230072969 + 3 ^ 40 * 5173276 * 2
def baseEnd_5173276 : Nat := 2656377146369006767558543

theorem tailTrace_5173276 : CollatzResearch.WordTrace tailWord_5173276 prefixEnd_5173276 2656377146369006767558543 := by
  unfold tailWord_5173276
  simp only [CollatzResearch.WordTrace]
  refine ⟨94342438403056026022437841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125789917870741368029917121 94342438403056026022437841)
  ·
    refine ⟨70756828802292019516828381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94342438403056026022437841 70756828802292019516828381)
    ·
      refine ⟨26533810800859507318810643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70756828802292019516828381 26533810800859507318810643)
      ·
        refine ⟨39800716201289260978215965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26533810800859507318810643 39800716201289260978215965)
        ·
          refine ⟨14925268575483472866830987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39800716201289260978215965 14925268575483472866830987)
          ·
            refine ⟨22387902863225209300246481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14925268575483472866830987 22387902863225209300246481)
            ·
              refine ⟨16790927147418906975184861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22387902863225209300246481 16790927147418906975184861)
              ·
                refine ⟨6296597680282090115694323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16790927147418906975184861 6296597680282090115694323)
                ·
                  refine ⟨9444896520423135173541485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296597680282090115694323 9444896520423135173541485)
                  ·
                    refine ⟨3541836195158675690078057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9444896520423135173541485 3541836195158675690078057)
                    ·
                      refine ⟨2656377146369006767558543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541836195158675690078057 2656377146369006767558543)
                      ·
                        rfl

theorem cell23_5173276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_5173276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173276 prefixEnd_5173276 := by exact prefixLift 5173276
  have htrace : WordTrace (prefixWord ++ tailWord_5173276) baseStart_5173276 baseEnd_5173276 := by
    simpa [prefixWord, tailWord_5173276, baseEnd_5173276] using wordTrace_append hprefix tailTrace_5173276
  have hstable : (prefixWord ++ tailWord_5173276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173276).length < 2 ^ (prefixWord ++ tailWord_5173276).sum := by decide
  have hdescent : baseEnd_5173276 < baseStart_5173276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173295 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 7]
def baseStart_5173295 : Nat := 118140960795 + 5173295 * 2 ^ 59
def prefixEnd_5173295 : Nat := 4983230072969 + 3 ^ 40 * 5173295 * 2
def baseEnd_5173295 : Nat := 295154100277938021468995

theorem tailTrace_5173295 : CollatzResearch.WordTrace tailWord_5173295 prefixEnd_5173295 295154100277938021468995 := by
  unfold tailWord_5173295
  simp only [CollatzResearch.WordTrace]
  refine ⟨188685569793043218289817339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125790379862028812193211559 188685569793043218289817339)
  ·
    refine ⟨283028354689564827434726009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188685569793043218289817339 283028354689564827434726009)
    ·
      refine ⟨212271266017173620576044507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283028354689564827434726009 212271266017173620576044507)
      ·
        refine ⟨318406899025760430864066761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212271266017173620576044507 318406899025760430864066761)
        ·
          refine ⟨238805174269320323148050071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318406899025760430864066761 238805174269320323148050071)
          ·
            refine ⟨358207761403980484722075107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238805174269320323148050071 358207761403980484722075107)
            ·
              refine ⟨537311642105970727083112661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358207761403980484722075107 537311642105970727083112661)
              ·
                refine ⟨12593241611858688916010453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 537311642105970727083112661 12593241611858688916010453)
                ·
                  refine ⟨295154100277938021468995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12593241611858688916010453 295154100277938021468995)
                  ·
                    rfl

theorem cell23_5173295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 7].length) (baseStart_5173295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173295 prefixEnd_5173295 := by exact prefixLift 5173295
  have htrace : WordTrace (prefixWord ++ tailWord_5173295) baseStart_5173295 baseEnd_5173295 := by
    simpa [prefixWord, tailWord_5173295, baseEnd_5173295] using wordTrace_append hprefix tailTrace_5173295
  have hstable : (prefixWord ++ tailWord_5173295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173295).length < 2 ^ (prefixWord ++ tailWord_5173295).sum := by decide
  have hdescent : baseEnd_5173295 < baseStart_5173295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173310 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_5173310 : Nat := 118140960795 + 5173310 * 2 ^ 59
def prefixEnd_5173310 : Nat := 4983230072969 + 3 ^ 40 * 5173310 * 2
def baseEnd_5173310 : Nat := 2656394604711259634533387

theorem tailTrace_5173310 : CollatzResearch.WordTrace tailWord_5173310 prefixEnd_5173310 2656394604711259634533387 := by
  unfold tailWord_5173310
  simp only [CollatzResearch.WordTrace]
  refine ⟨23585764610998609481451673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125790744591992583901075589 23585764610998609481451673)
  ·
    refine ⟨17689323458248957111088755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23585764610998609481451673 17689323458248957111088755)
    ·
      refine ⟨26533985187373435666633133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17689323458248957111088755 26533985187373435666633133)
      ·
        refine ⟨9950244445265038374987425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26533985187373435666633133 9950244445265038374987425)
        ·
          refine ⟨7462683333948778781240569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9950244445265038374987425 7462683333948778781240569)
          ·
            refine ⟨5597012500461584085930427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7462683333948778781240569 5597012500461584085930427)
            ·
              refine ⟨8395518750692376128895641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5597012500461584085930427 8395518750692376128895641)
              ·
                refine ⟨6296639063019282096671731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8395518750692376128895641 6296639063019282096671731)
                ·
                  refine ⟨9444958594528923145007597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6296639063019282096671731 9444958594528923145007597)
                  ·
                    refine ⟨3541859472948346179377849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9444958594528923145007597 3541859472948346179377849)
                    ·
                      refine ⟨2656394604711259634533387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541859472948346179377849 2656394604711259634533387)
                      ·
                        rfl

theorem cell23_5173310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_5173310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173310 prefixEnd_5173310 := by exact prefixLift 5173310
  have htrace : WordTrace (prefixWord ++ tailWord_5173310) baseStart_5173310 baseEnd_5173310 := by
    simpa [prefixWord, tailWord_5173310, baseEnd_5173310] using wordTrace_append hprefix tailTrace_5173310
  have hstable : (prefixWord ++ tailWord_5173310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173310).length < 2 ^ (prefixWord ++ tailWord_5173310).sum := by decide
  have hdescent : baseEnd_5173310 < baseStart_5173310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173322 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_5173322 : Nat := 118140960795 + 5173322 * 2 ^ 59
def prefixEnd_5173322 : Nat := 4983230072969 + 3 ^ 40 * 5173322 * 2
def baseEnd_5173322 : Nat := 2656400766479113587583331

theorem tailTrace_5173322 : CollatzResearch.WordTrace tailWord_5173322 prefixEnd_5173322 2656400766479113587583331 := by
  unfold tailWord_5173322
  simp only [CollatzResearch.WordTrace]
  refine ⟨47171638640986350475262555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125791036375963601267366813 47171638640986350475262555)
  ·
    refine ⟨70757457961479525712893833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47171638640986350475262555 70757457961479525712893833)
    ·
      refine ⟨53068093471109644284670375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70757457961479525712893833 53068093471109644284670375)
      ·
        refine ⟨79602140206664466427005563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53068093471109644284670375 79602140206664466427005563)
        ·
          refine ⟨119403210309996699640508345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79602140206664466427005563 119403210309996699640508345)
          ·
            refine ⟨89552407732497524730381259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119403210309996699640508345 89552407732497524730381259)
            ·
              refine ⟨134328611598746287095571889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89552407732497524730381259 134328611598746287095571889)
              ·
                refine ⟨100746458699059715321678917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134328611598746287095571889 100746458699059715321678917)
                ·
                  refine ⟨18889961006073696622814797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100746458699059715321678917 18889961006073696622814797)
                  ·
                    refine ⟨7083735377277636233555549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18889961006073696622814797 7083735377277636233555549)
                    ·
                      refine ⟨2656400766479113587583331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7083735377277636233555549 2656400766479113587583331)
                      ·
                        rfl

theorem cell23_5173322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_5173322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173322 prefixEnd_5173322 := by exact prefixLift 5173322
  have htrace : WordTrace (prefixWord ++ tailWord_5173322) baseStart_5173322 baseEnd_5173322 := by
    simpa [prefixWord, tailWord_5173322, baseEnd_5173322] using wordTrace_append hprefix tailTrace_5173322
  have hstable : (prefixWord ++ tailWord_5173322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173322).length < 2 ^ (prefixWord ++ tailWord_5173322).sum := by decide
  have hdescent : baseEnd_5173322 < baseStart_5173322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173349 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 2, 5, 2]
def baseStart_5173349 : Nat := 118140960795 + 5173349 * 2 ^ 59
def prefixEnd_5173349 : Nat := 4983230072969 + 3 ^ 40 * 5173349 * 2
def baseEnd_5173349 : Nat := 2656414630456784981945707

theorem tailTrace_5173349 : CollatzResearch.WordTrace tailWord_5173349 prefixEnd_5173349 2656414630456784981945707 := by
  unfold tailWord_5173349
  simp only [CollatzResearch.WordTrace]
  refine ⟨188687539334847585512283101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125791692889898390341522067 188687539334847585512283101)
  ·
    refine ⟨70757827250567844567106163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188687539334847585512283101 70757827250567844567106163)
    ·
      refine ⟨106136740875851766850659245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70757827250567844567106163 106136740875851766850659245)
      ·
        refine ⟨39801277828444412568997217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106136740875851766850659245 39801277828444412568997217)
        ·
          refine ⟨29850958371333309426747913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39801277828444412568997217 29850958371333309426747913)
          ·
            refine ⟨22388218778499982070060935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29850958371333309426747913 22388218778499982070060935)
            ·
              refine ⟨33582328167749973105091403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22388218778499982070060935 33582328167749973105091403)
              ·
                refine ⟨50373492251624959657637105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33582328167749973105091403 50373492251624959657637105)
                ·
                  refine ⟨37780119188718719743227829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50373492251624959657637105 37780119188718719743227829)
                  ·
                    refine ⟨3541886173942379975927609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37780119188718719743227829 3541886173942379975927609)
                    ·
                      refine ⟨2656414630456784981945707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3541886173942379975927609 2656414630456784981945707)
                      ·
                        rfl

theorem cell23_5173349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_5173349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173349 prefixEnd_5173349 := by exact prefixLift 5173349
  have htrace : WordTrace (prefixWord ++ tailWord_5173349) baseStart_5173349 baseEnd_5173349 := by
    simpa [prefixWord, tailWord_5173349, baseEnd_5173349] using wordTrace_append hprefix tailTrace_5173349
  have hstable : (prefixWord ++ tailWord_5173349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173349).length < 2 ^ (prefixWord ++ tailWord_5173349).sum := by decide
  have hdescent : baseEnd_5173349 < baseStart_5173349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173379 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 4]
def baseStart_5173379 : Nat := 118140960795 + 5173379 * 2 ^ 59
def prefixEnd_5173379 : Nat := 4983230072969 + 3 ^ 40 * 5173379 * 2
def baseEnd_5173379 : Nat := 2656430034876419864570569

theorem tailTrace_5173379 : CollatzResearch.WordTrace tailWord_5173379 prefixEnd_5173379 2656430034876419864570569 := by
  unfold tailWord_5173379
  simp only [CollatzResearch.WordTrace]
  refine ⟨188688633524738900635875191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125792422349825933757250127 188688633524738900635875191)
  ·
    refine ⟨283032950287108350953812787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188688633524738900635875191 283032950287108350953812787)
    ·
      refine ⟨424549425430662526430719181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283032950287108350953812787 424549425430662526430719181)
      ·
        refine ⟨159206034536498447411519693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424549425430662526430719181 159206034536498447411519693)
        ·
          refine ⟨59702262951186917779319885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159206034536498447411519693 59702262951186917779319885)
          ·
            refine ⟨22388348606695094167244957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59702262951186917779319885 22388348606695094167244957)
            ·
              refine ⟨8395630727510660312716859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22388348606695094167244957 8395630727510660312716859)
              ·
                refine ⟨12593446091265990469075289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8395630727510660312716859 12593446091265990469075289)
                ·
                  refine ⟨9445084568449492851806467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12593446091265990469075289 9445084568449492851806467)
                  ·
                    refine ⟨14167626852674239277709701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9445084568449492851806467 14167626852674239277709701)
                    ·
                      refine ⟨2656430034876419864570569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14167626852674239277709701 2656430034876419864570569)
                      ·
                        rfl

theorem cell23_5173379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_5173379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173379 prefixEnd_5173379 := by exact prefixLift 5173379
  have htrace : WordTrace (prefixWord ++ tailWord_5173379) baseStart_5173379 baseEnd_5173379 := by
    simpa [prefixWord, tailWord_5173379, baseEnd_5173379] using wordTrace_append hprefix tailTrace_5173379
  have hstable : (prefixWord ++ tailWord_5173379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173379).length < 2 ^ (prefixWord ++ tailWord_5173379).sum := by decide
  have hdescent : baseEnd_5173379 < baseStart_5173379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173533 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_5173533 : Nat := 118140960795 + 5173533 * 2 ^ 59
def prefixEnd_5173533 : Nat := 4983230072969 + 3 ^ 40 * 5173533 * 2
def baseEnd_5173533 : Nat := 2656509110897212262044861

theorem tailTrace_5173533 : CollatzResearch.WordTrace tailWord_5173533 prefixEnd_5173533 2656509110897212262044861 := by
  unfold tailWord_5173533
  simp only [CollatzResearch.WordTrace]
  refine ⟨188694250366180984936981253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125796166910787323291320835 188694250366180984936981253)
  ·
    refine ⟨35380171943658934675683985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188694250366180984936981253 35380171943658934675683985)
    ·
      refine ⟨26535128957744201006762989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35380171943658934675683985 26535128957744201006762989)
      ·
        refine ⟨9950673359154075377536121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26535128957744201006762989 9950673359154075377536121)
        ·
          refine ⟨7463005019365556533152091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9950673359154075377536121 7463005019365556533152091)
          ·
            refine ⟨11194507529048334799728137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463005019365556533152091 11194507529048334799728137)
            ·
              refine ⟨8395880646786251099796103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11194507529048334799728137 8395880646786251099796103)
              ·
                refine ⟨12593820970179376649694155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8395880646786251099796103 12593820970179376649694155)
                ·
                  refine ⟨18890731455269064974541233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12593820970179376649694155 18890731455269064974541233)
                  ·
                    refine ⟨14168048591451798730905925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18890731455269064974541233 14168048591451798730905925)
                    ·
                      refine ⟨2656509110897212262044861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14168048591451798730905925 2656509110897212262044861)
                      ·
                        rfl

theorem cell23_5173533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_5173533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173533 prefixEnd_5173533 := by exact prefixLift 5173533
  have htrace : WordTrace (prefixWord ++ tailWord_5173533) baseStart_5173533 baseEnd_5173533 := by
    simpa [prefixWord, tailWord_5173533, baseEnd_5173533] using wordTrace_append hprefix tailTrace_5173533
  have hstable : (prefixWord ++ tailWord_5173533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173533).length < 2 ^ (prefixWord ++ tailWord_5173533).sum := by decide
  have hdescent : baseEnd_5173533 < baseStart_5173533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173536 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 3]
def baseStart_5173536 : Nat := 118140960795 + 5173536 * 2 ^ 59
def prefixEnd_5173536 : Nat := 4983230072969 + 3 ^ 40 * 5173536 * 2
def baseEnd_5173536 : Nat := 2656510651339175750307347

theorem tailTrace_5173536 : CollatzResearch.WordTrace tailWord_5173536 prefixEnd_5173536 2656510651339175750307347 := by
  unfold tailWord_5173536
  simp only [CollatzResearch.WordTrace]
  refine ⟨94347179892585058224670231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125796239856780077632893641 94347179892585058224670231)
  ·
    refine ⟨141520769838877587337005347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94347179892585058224670231 141520769838877587337005347)
    ·
      refine ⟨212281154758316381005508021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141520769838877587337005347 212281154758316381005508021)
      ·
        refine ⟨19901358258592160719266377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 212281154758316381005508021 19901358258592160719266377)
        ·
          refine ⟨14926018693944120539449783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19901358258592160719266377 14926018693944120539449783)
          ·
            refine ⟨22389028040916180809174675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14926018693944120539449783 22389028040916180809174675)
            ·
              refine ⟨33583542061374271213762013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22389028040916180809174675 33583542061374271213762013)
              ·
                refine ⟨12593828273015351705160755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33583542061374271213762013 12593828273015351705160755)
                ·
                  refine ⟨18890742409523027557741133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12593828273015351705160755 18890742409523027557741133)
                  ·
                    refine ⟨7084028403571135334152925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18890742409523027557741133 7084028403571135334152925)
                    ·
                      refine ⟨2656510651339175750307347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7084028403571135334152925 2656510651339175750307347)
                      ·
                        rfl

theorem cell23_5173536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_5173536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173536 prefixEnd_5173536 := by exact prefixLift 5173536
  have htrace : WordTrace (prefixWord ++ tailWord_5173536) baseStart_5173536 baseEnd_5173536 := by
    simpa [prefixWord, tailWord_5173536, baseEnd_5173536] using wordTrace_append hprefix tailTrace_5173536
  have hstable : (prefixWord ++ tailWord_5173536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173536).length < 2 ^ (prefixWord ++ tailWord_5173536).sum := by decide
  have hdescent : baseEnd_5173536 < baseStart_5173536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173576 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_5173576 : Nat := 118140960795 + 5173576 * 2 ^ 59
def prefixEnd_5173576 : Nat := 4983230072969 + 3 ^ 40 * 5173576 * 2
def baseEnd_5173576 : Nat := 2656531190565355593807163

theorem tailTrace_5173576 : CollatzResearch.WordTrace tailWord_5173576 prefixEnd_5173576 2656531190565355593807163 := by
  unfold tailWord_5173576
  simp only [CollatzResearch.WordTrace]
  refine ⟨94347909352512601640398291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125797212470016802187197721 94347909352512601640398291)
  ·
    refine ⟨141521864028768902460597437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94347909352512601640398291 141521864028768902460597437)
    ·
      refine ⟨53070699010788338422724039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141521864028768902460597437 53070699010788338422724039)
      ·
        refine ⟨79606048516182507634086059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53070699010788338422724039 79606048516182507634086059)
        ·
          refine ⟨119409072774273761451129089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79606048516182507634086059 119409072774273761451129089)
          ·
            refine ⟨89556804580705321088346817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119409072774273761451129089 89556804580705321088346817)
            ·
              refine ⟨67167603435528990816260113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89556804580705321088346817 67167603435528990816260113)
              ·
                refine ⟨50375702576646743112195085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67167603435528990816260113 50375702576646743112195085)
                ·
                  refine ⟨18890888466242528667073157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50375702576646743112195085 18890888466242528667073157)
                  ·
                    refine ⟨3542041587420474125076217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18890888466242528667073157 3542041587420474125076217)
                    ·
                      refine ⟨2656531190565355593807163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3542041587420474125076217 2656531190565355593807163)
                      ·
                        rfl

theorem cell23_5173576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_5173576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173576 prefixEnd_5173576 := by exact prefixLift 5173576
  have htrace : WordTrace (prefixWord ++ tailWord_5173576) baseStart_5173576 baseEnd_5173576 := by
    simpa [prefixWord, tailWord_5173576, baseEnd_5173576] using wordTrace_append hprefix tailTrace_5173576
  have hstable : (prefixWord ++ tailWord_5173576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173576).length < 2 ^ (prefixWord ++ tailWord_5173576).sum := by decide
  have hdescent : baseEnd_5173576 < baseStart_5173576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173579 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 3]
def baseStart_5173579 : Nat := 118140960795 + 5173579 * 2 ^ 59
def prefixEnd_5173579 : Nat := 4983230072969 + 3 ^ 40 * 5173579 * 2
def baseEnd_5173579 : Nat := 2656532731007319082069649

theorem tailTrace_5173579 : CollatzResearch.WordTrace tailWord_5173579 prefixEnd_5173579 2656532731007319082069649 := by
  unfold tailWord_5173579
  simp only [CollatzResearch.WordTrace]
  refine ⟨188695928124014334793155791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125797285416009556528770527 188695928124014334793155791)
  ·
    refine ⟨283043892186021502189733687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188695928124014334793155791 283043892186021502189733687)
    ·
      refine ⟨424565838279032253284600531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283043892186021502189733687 424565838279032253284600531)
      ·
        refine ⟨636848757418548379926900797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424565838279032253284600531 636848757418548379926900797)
        ·
          refine ⟨238818284031955642472587799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 636848757418548379926900797 238818284031955642472587799)
          ·
            refine ⟨358227426047933463708881699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238818284031955642472587799 358227426047933463708881699)
            ·
              refine ⟨537341139071900195563322549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358227426047933463708881699 537341139071900195563322549)
              ·
                refine ⟨50375731787990643334061489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 537341139071900195563322549 50375731787990643334061489)
                ·
                  refine ⟨37781798840992982500546117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50375731787990643334061489 37781798840992982500546117)
                  ·
                    refine ⟨7084087282686184218852397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37781798840992982500546117 7084087282686184218852397)
                    ·
                      refine ⟨2656532731007319082069649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7084087282686184218852397 2656532731007319082069649)
                      ·
                        rfl

theorem cell23_5173579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 3].length) (baseStart_5173579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173579 prefixEnd_5173579 := by exact prefixLift 5173579
  have htrace : WordTrace (prefixWord ++ tailWord_5173579) baseStart_5173579 baseEnd_5173579 := by
    simpa [prefixWord, tailWord_5173579, baseEnd_5173579] using wordTrace_append hprefix tailTrace_5173579
  have hstable : (prefixWord ++ tailWord_5173579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173579).length < 2 ^ (prefixWord ++ tailWord_5173579).sum := by decide
  have hdescent : baseEnd_5173579 < baseStart_5173579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173599 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 7]
def baseStart_5173599 : Nat := 118140960795 + 5173599 * 2 ^ 59
def prefixEnd_5173599 : Nat := 4983230072969 + 3 ^ 40 * 5173599 * 2
def baseEnd_5173599 : Nat := 295171444513378778202173

theorem tailTrace_5173599 : CollatzResearch.WordTrace tailWord_5173599 prefixEnd_5173599 295171444513378778202173 := by
  unfold tailWord_5173599
  simp only [CollatzResearch.WordTrace]
  refine ⟨188696657583941878208883851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125797771722627918805922567 188696657583941878208883851)
  ·
    refine ⟨283044986375912817313325777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188696657583941878208883851 283044986375912817313325777)
    ·
      refine ⟨212283739781934612984994333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283044986375912817313325777 212283739781934612984994333)
      ·
        refine ⟨79606402418225479869372875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212283739781934612984994333 79606402418225479869372875)
        ·
          refine ⟨119409603627338219804059313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79606402418225479869372875 119409603627338219804059313)
          ·
            refine ⟨89557202720503664853044485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119409603627338219804059313 89557202720503664853044485)
            ·
              refine ⟨16791975510094437159945841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89557202720503664853044485 16791975510094437159945841)
              ·
                refine ⟨12593981632570827869959381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16791975510094437159945841 12593981632570827869959381)
                ·
                  refine ⟨295171444513378778202173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12593981632570827869959381 295171444513378778202173)
                  ·
                    rfl

theorem cell23_5173599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 7].length) (baseStart_5173599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173599 prefixEnd_5173599 := by exact prefixLift 5173599
  have htrace : WordTrace (prefixWord ++ tailWord_5173599) baseStart_5173599 baseEnd_5173599 := by
    simpa [prefixWord, tailWord_5173599, baseEnd_5173599] using wordTrace_append hprefix tailTrace_5173599
  have hstable : (prefixWord ++ tailWord_5173599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173599).length < 2 ^ (prefixWord ++ tailWord_5173599).sum := by decide
  have hdescent : baseEnd_5173599 < baseStart_5173599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173610 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5173610 : Nat := 118140960795 + 5173610 * 2 ^ 59
def prefixEnd_5173610 : Nat := 4983230072969 + 3 ^ 40 * 5173610 * 2
def baseEnd_5173610 : Nat := 2656548648907608460782007

theorem tailTrace_5173610 : CollatzResearch.WordTrace tailWord_5173610 prefixEnd_5173610 2656548648907608460782007 := by
  unfold tailWord_5173610
  simp only [CollatzResearch.WordTrace]
  refine ⟨47174264696725506771883571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125798039191268018058356189 47174264696725506771883571)
  ·
    refine ⟨70761397045088260157825357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47174264696725506771883571 70761397045088260157825357)
    ·
      refine ⟨26535523891908097559184509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70761397045088260157825357 26535523891908097559184509)
      ·
        refine ⟨9950821459465536584694191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26535523891908097559184509 9950821459465536584694191)
        ·
          refine ⟨14926232189198304877041287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9950821459465536584694191 14926232189198304877041287)
          ·
            refine ⟨22389348283797457315561931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14926232189198304877041287 22389348283797457315561931)
            ·
              refine ⟨33584022425696185973342897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22389348283797457315561931 33584022425696185973342897)
              ·
                refine ⟨25188016819272139480007173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33584022425696185973342897 25188016819272139480007173)
                ·
                  refine ⟨4722753153613526152501345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25188016819272139480007173 4722753153613526152501345)
                  ·
                    refine ⟨3542064865210144614376009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4722753153613526152501345 3542064865210144614376009)
                    ·
                      refine ⟨2656548648907608460782007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3542064865210144614376009 2656548648907608460782007)
                      ·
                        rfl

theorem cell23_5173610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5173610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173610 prefixEnd_5173610 := by exact prefixLift 5173610
  have htrace : WordTrace (prefixWord ++ tailWord_5173610) baseStart_5173610 baseEnd_5173610 := by
    simpa [prefixWord, tailWord_5173610, baseEnd_5173610] using wordTrace_append hprefix tailTrace_5173610
  have hstable : (prefixWord ++ tailWord_5173610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173610).length < 2 ^ (prefixWord ++ tailWord_5173610).sum := by decide
  have hdescent : baseEnd_5173610 < baseStart_5173610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173633 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 7]
def baseStart_5173633 : Nat := 118140960795 + 5173633 * 2 ^ 59
def prefixEnd_5173633 : Nat := 4983230072969 + 3 ^ 40 * 5173633 * 2
def baseEnd_5173633 : Nat := 295173384329184652310489

theorem tailTrace_5173633 : CollatzResearch.WordTrace tailWord_5173633 prefixEnd_5173633 295173384329184652310489 := by
  unfold tailWord_5173633
  simp only [CollatzResearch.WordTrace]
  refine ⟨188697897665818702015621553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125798598443879134677081035 188697897665818702015621553)
  ·
    refine ⟨141523423249364026511716165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188697897665818702015621553 141523423249364026511716165)
    ·
      refine ⟨26535641859255754970946781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141523423249364026511716165 26535641859255754970946781)
      ·
        refine ⟨9950865697220908114105043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26535641859255754970946781 9950865697220908114105043)
        ·
          refine ⟨14926298545831362171157565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9950865697220908114105043 14926298545831362171157565)
          ·
            refine ⟨5597361954686760814184087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14926298545831362171157565 5597361954686760814184087)
            ·
              refine ⟨8396042932030141221276131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5597361954686760814184087 8396042932030141221276131)
              ·
                refine ⟨12594064398045211831914197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8396042932030141221276131 12594064398045211831914197)
                ·
                  refine ⟨295173384329184652310489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12594064398045211831914197 295173384329184652310489)
                  ·
                    rfl

theorem cell23_5173633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 7].length) (baseStart_5173633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173633 prefixEnd_5173633 := by exact prefixLift 5173633
  have htrace : WordTrace (prefixWord ++ tailWord_5173633) baseStart_5173633 baseEnd_5173633 := by
    simpa [prefixWord, tailWord_5173633, baseEnd_5173633] using wordTrace_append hprefix tailTrace_5173633
  have hstable : (prefixWord ++ tailWord_5173633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173633).length < 2 ^ (prefixWord ++ tailWord_5173633).sum := by decide
  have hdescent : baseEnd_5173633 < baseStart_5173633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173706 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 6]
def baseStart_5173706 : Nat := 118140960795 + 5173706 * 2 ^ 59
def prefixEnd_5173706 : Nat := 4983230072969 + 3 ^ 40 * 5173706 * 2
def baseEnd_5173706 : Nat := 295177549227826676131285

theorem tailTrace_5173706 : CollatzResearch.WordTrace tailWord_5173706 prefixEnd_5173706 295177549227826676131285 := by
  unfold tailWord_5173706
  simp only [CollatzResearch.WordTrace]
  refine ⟨47175140048638558870757243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125800373463036156988685981 47175140048638558870757243)
  ·
    refine ⟨70762710072957838306135865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47175140048638558870757243 70762710072957838306135865)
    ·
      refine ⟨53072032554718378729601899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70762710072957838306135865 53072032554718378729601899)
      ·
        refine ⟨79608048832077568094402849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53072032554718378729601899 79608048832077568094402849)
        ·
          refine ⟨59706036624058176070802137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79608048832077568094402849 59706036624058176070802137)
          ·
            refine ⟨44779527468043632053101603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59706036624058176070802137 44779527468043632053101603)
            ·
              refine ⟨67169291202065448079652405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44779527468043632053101603 67169291202065448079652405)
              ·
                refine ⟨6297121050193635757467413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67169291202065448079652405 6297121050193635757467413)
                ·
                  refine ⟨295177549227826676131285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6297121050193635757467413 295177549227826676131285)
                  ·
                    rfl

theorem cell23_5173706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_5173706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173706 prefixEnd_5173706 := by exact prefixLift 5173706
  have htrace : WordTrace (prefixWord ++ tailWord_5173706) baseStart_5173706 baseEnd_5173706 := by
    simpa [prefixWord, tailWord_5173706, baseEnd_5173706] using wordTrace_append hprefix tailTrace_5173706
  have hstable : (prefixWord ++ tailWord_5173706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173706).length < 2 ^ (prefixWord ++ tailWord_5173706).sum := by decide
  have hdescent : baseEnd_5173706 < baseStart_5173706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173743 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 4, 3, 2]
def baseStart_5173743 : Nat := 118140960795 + 5173743 * 2 ^ 59
def prefixEnd_5173743 : Nat := 4983230072969 + 3 ^ 40 * 5173743 * 2
def baseEnd_5173743 : Nat := 2656616941834656440418895

theorem tailTrace_5173743 : CollatzResearch.WordTrace tailWord_5173743 prefixEnd_5173743 2656616941834656440418895 := by
  unfold tailWord_5173743
  simp only [CollatzResearch.WordTrace]
  refine ⟨188701909695420190802125883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125801273130280127201417255 188701909695420190802125883)
  ·
    refine ⟨283052864543130286203188825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188701909695420190802125883 283052864543130286203188825)
    ·
      refine ⟨212289648407347714652391619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283052864543130286203188825 212289648407347714652391619)
      ·
        refine ⟨318434472611021571978587429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212289648407347714652391619 318434472611021571978587429)
        ·
          refine ⟨59706463614566544745985143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318434472611021571978587429 59706463614566544745985143)
          ·
            refine ⟨89559695421849817118977715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59706463614566544745985143 89559695421849817118977715)
            ·
              refine ⟨134339543132774725678466573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89559695421849817118977715 134339543132774725678466573)
              ·
                refine ⟨50377328674790522129424965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134339543132774725678466573 50377328674790522129424965)
                ·
                  refine ⟨9445749126523222899267181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50377328674790522129424965 9445749126523222899267181)
                  ·
                    refine ⟨3542155922446208587225193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9445749126523222899267181 3542155922446208587225193)
                    ·
                      refine ⟨2656616941834656440418895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3542155922446208587225193 2656616941834656440418895)
                      ·
                        rfl

theorem cell23_5173743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 3, 2].length) (baseStart_5173743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173743 prefixEnd_5173743 := by exact prefixLift 5173743
  have htrace : WordTrace (prefixWord ++ tailWord_5173743) baseStart_5173743 baseEnd_5173743 := by
    simpa [prefixWord, tailWord_5173743, baseEnd_5173743] using wordTrace_append hprefix tailTrace_5173743
  have hstable : (prefixWord ++ tailWord_5173743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173743).length < 2 ^ (prefixWord ++ tailWord_5173743).sum := by decide
  have hdescent : baseEnd_5173743 < baseStart_5173743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173784 : List Nat := [2, 1, 2, 3, 3, 3, 1, 3, 1, 1, 3]
def baseStart_5173784 : Nat := 118140960795 + 5173784 * 2 ^ 59
def prefixEnd_5173784 : Nat := 4983230072969 + 3 ^ 40 * 5173784 * 2
def baseEnd_5173784 : Nat := 2656637994541490780006207

theorem tailTrace_5173784 : CollatzResearch.WordTrace tailWord_5173784 prefixEnd_5173784 2656637994541490780006207 := by
  unfold tailWord_5173784
  simp only [CollatzResearch.WordTrace]
  refine ⟨94351702544135827402184203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125802270058847769869578937 94351702544135827402184203)
  ·
    refine ⟨141527553816203741103276305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94351702544135827402184203 141527553816203741103276305)
    ·
      refine ⟨106145665362152805827457229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141527553816203741103276305 106145665362152805827457229)
      ·
        refine ⟨39804624510807302185296461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106145665362152805827457229 39804624510807302185296461)
        ·
          refine ⟨14926734191552738319486173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39804624510807302185296461 14926734191552738319486173)
          ·
            refine ⟨5597525321832276869807315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14926734191552738319486173 5597525321832276869807315)
            ·
              refine ⟨8396287982748415304710973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5597525321832276869807315 8396287982748415304710973)
              ·
                refine ⟨3148607993530655739266615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8396287982748415304710973 3148607993530655739266615)
                ·
                  refine ⟨4722911990295983608899923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3148607993530655739266615 4722911990295983608899923)
                  ·
                    refine ⟨7084367985443975413349885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4722911990295983608899923 7084367985443975413349885)
                    ·
                      refine ⟨2656637994541490780006207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7084367985443975413349885 2656637994541490780006207)
                      ·
                        rfl

theorem cell23_5173784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_5173784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173784 prefixEnd_5173784 := by exact prefixLift 5173784
  have htrace : WordTrace (prefixWord ++ tailWord_5173784) baseStart_5173784 baseEnd_5173784 := by
    simpa [prefixWord, tailWord_5173784, baseEnd_5173784] using wordTrace_append hprefix tailTrace_5173784
  have hstable : (prefixWord ++ tailWord_5173784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173784).length < 2 ^ (prefixWord ++ tailWord_5173784).sum := by decide
  have hdescent : baseEnd_5173784 < baseStart_5173784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173793 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_5173793 : Nat := 118140960795 + 5173793 * 2 ^ 59
def prefixEnd_5173793 : Nat := 4983230072969 + 3 ^ 40 * 5173793 * 2
def baseEnd_5173793 : Nat := 2656642615867381244793665

theorem tailTrace_5173793 : CollatzResearch.WordTrace tailWord_5173793 prefixEnd_5173793 2656642615867381244793665 := by
  unfold tailWord_5173793
  simp only [CollatzResearch.WordTrace]
  refine ⟨188703733345239049341446033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125802488896826032894297355 188703733345239049341446033)
  ·
    refine ⟨141527800008929287006084525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188703733345239049341446033 141527800008929287006084525)
    ·
      refine ⟨53072925003348482627281697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141527800008929287006084525 53072925003348482627281697)
      ·
        refine ⟨39804693752511361970461273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53072925003348482627281697 39804693752511361970461273)
        ·
          refine ⟨29853520314383521477845955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39804693752511361970461273 29853520314383521477845955)
          ·
            refine ⟨44780280471575282216768933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29853520314383521477845955 44780280471575282216768933)
            ·
              refine ⟨8396302588420365415644175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44780280471575282216768933 8396302588420365415644175)
              ·
                refine ⟨12594453882630548123466263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8396302588420365415644175 12594453882630548123466263)
                ·
                  refine ⟨18891680823945822185199395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12594453882630548123466263 18891680823945822185199395)
                  ·
                    refine ⟨28337521235918733277799093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18891680823945822185199395 28337521235918733277799093)
                    ·
                      refine ⟨2656642615867381244793665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28337521235918733277799093 2656642615867381244793665)
                      ·
                        rfl

theorem cell23_5173793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_5173793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173793 prefixEnd_5173793 := by exact prefixLift 5173793
  have htrace : WordTrace (prefixWord ++ tailWord_5173793) baseStart_5173793 baseEnd_5173793 := by
    simpa [prefixWord, tailWord_5173793, baseEnd_5173793] using wordTrace_append hprefix tailTrace_5173793
  have hstable : (prefixWord ++ tailWord_5173793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173793).length < 2 ^ (prefixWord ++ tailWord_5173793).sum := by decide
  have hdescent : baseEnd_5173793 < baseStart_5173793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173800 : List Nat := [2, 1, 5, 2, 1, 1, 2, 1, 4, 4]
def baseStart_5173800 : Nat := 118140960795 + 5173800 * 2 ^ 59
def prefixEnd_5173800 : Nat := 4983230072969 + 3 ^ 40 * 5173800 * 2
def baseEnd_5173800 : Nat := 885548736743987572468711

theorem tailTrace_5173800 : CollatzResearch.WordTrace tailWord_5173800 prefixEnd_5173800 885548736743987572468711 := by
  unfold tailWord_5173800
  simp only [CollatzResearch.WordTrace]
  refine ⟨94351994328106844768475427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125802659104142459691300569 94351994328106844768475427)
  ·
    refine ⟨141527991492160267152713141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94351994328106844768475427 141527991492160267152713141)
    ·
      refine ⟨13268249202390025045566857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141527991492160267152713141 13268249202390025045566857)
      ·
        refine ⟨9951186901792518784175143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13268249202390025045566857 9951186901792518784175143)
        ·
          refine ⟨14926780352688778176262715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9951186901792518784175143 14926780352688778176262715)
          ·
            refine ⟨22390170529033167264394073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14926780352688778176262715 22390170529033167264394073)
            ·
              refine ⟨16792627896774875448295555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22390170529033167264394073 16792627896774875448295555)
              ·
                refine ⟨25188941845162313172443333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16792627896774875448295555 25188941845162313172443333)
                ·
                  refine ⟨4722926595967933719833125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25188941845162313172443333 4722926595967933719833125)
                  ·
                    refine ⟨885548736743987572468711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4722926595967933719833125 885548736743987572468711)
                    ·
                      rfl

theorem cell23_5173800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_5173800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173800 prefixEnd_5173800 := by exact prefixLift 5173800
  have htrace : WordTrace (prefixWord ++ tailWord_5173800) baseStart_5173800 baseEnd_5173800 := by
    simpa [prefixWord, tailWord_5173800, baseEnd_5173800] using wordTrace_append hprefix tailTrace_5173800
  have hstable : (prefixWord ++ tailWord_5173800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173800).length < 2 ^ (prefixWord ++ tailWord_5173800).sum := by decide
  have hdescent : baseEnd_5173800 < baseStart_5173800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173816 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 2, 2, 6]
def baseStart_5173816 : Nat := 118140960795 + 5173816 * 2 ^ 59
def prefixEnd_5173816 : Nat := 4983230072969 + 3 ^ 40 * 5173816 * 2
def baseEnd_5173816 : Nat := 2656654425922434654806059

theorem tailTrace_5173816 : CollatzResearch.WordTrace tailWord_5173816 prefixEnd_5173816 2656654425922434654806059 := by
  unfold tailWord_5173816
  simp only [CollatzResearch.WordTrace]
  refine ⟨94352286112077862134766651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125803048149437149513022201 94352286112077862134766651)
  ·
    refine ⟨141528429168116793202149977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94352286112077862134766651 141528429168116793202149977)
    ·
      refine ⟨106146321876087594901612483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141528429168116793202149977 106146321876087594901612483)
      ·
        refine ⟨159219482814131392352418725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106146321876087594901612483 159219482814131392352418725)
        ·
          refine ⟨29853653027649636066078511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159219482814131392352418725 29853653027649636066078511)
          ·
            refine ⟨44780479541474454099117767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29853653027649636066078511 44780479541474454099117767)
            ·
              refine ⟨67170719312211681148676651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44780479541474454099117767 67170719312211681148676651)
              ·
                refine ⟨100756078968317521723014977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67170719312211681148676651 100756078968317521723014977)
                ·
                  refine ⟨75567059226238141292261233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100756078968317521723014977 75567059226238141292261233)
                  ·
                    refine ⟨56675294419678605969195925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75567059226238141292261233 56675294419678605969195925)
                    ·
                      refine ⟨2656654425922434654806059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56675294419678605969195925 2656654425922434654806059)
                      ·
                        rfl

theorem cell23_5173816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_5173816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173816 prefixEnd_5173816 := by exact prefixLift 5173816
  have htrace : WordTrace (prefixWord ++ tailWord_5173816) baseStart_5173816 baseEnd_5173816 := by
    simpa [prefixWord, tailWord_5173816, baseEnd_5173816] using wordTrace_append hprefix tailTrace_5173816
  have hstable : (prefixWord ++ tailWord_5173816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173816).length < 2 ^ (prefixWord ++ tailWord_5173816).sum := by decide
  have hdescent : baseEnd_5173816 < baseStart_5173816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173823 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 3]
def baseStart_5173823 : Nat := 118140960795 + 5173823 * 2 ^ 59
def prefixEnd_5173823 : Nat := 4983230072969 + 3 ^ 40 * 5173823 * 2
def baseEnd_5173823 : Nat := 2656658020287016127418527

theorem tailTrace_5173823 : CollatzResearch.WordTrace tailWord_5173823 prefixEnd_5173823 2656658020287016127418527 := by
  unfold tailWord_5173823
  simp only [CollatzResearch.WordTrace]
  refine ⟨188704827535130364465038123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125803218356753576310025415 188704827535130364465038123)
  ·
    refine ⟨283057241302695546697557185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188704827535130364465038123 283057241302695546697557185)
    ·
      refine ⟨212292930977021660023167889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283057241302695546697557185 212292930977021660023167889)
      ·
        refine ⟨159219698232766245017375917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212292930977021660023167889 159219698232766245017375917)
        ·
          refine ⟨59707386837287341881515969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159219698232766245017375917 59707386837287341881515969)
          ·
            refine ⟨44780540127965506411136977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59707386837287341881515969 44780540127965506411136977)
            ·
              refine ⟨33585405095974129808352733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44780540127965506411136977 33585405095974129808352733)
              ·
                refine ⟨12594526910990298678132275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33585405095974129808352733 12594526910990298678132275)
                ·
                  refine ⟨18891790366485448017198413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12594526910990298678132275 18891790366485448017198413)
                  ·
                    refine ⟨7084421387432043006449405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18891790366485448017198413 7084421387432043006449405)
                    ·
                      refine ⟨2656658020287016127418527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7084421387432043006449405 2656658020287016127418527)
                      ·
                        rfl

theorem cell23_5173823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_5173823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173823 prefixEnd_5173823 := by exact prefixLift 5173823
  have htrace : WordTrace (prefixWord ++ tailWord_5173823) baseStart_5173823 baseEnd_5173823 := by
    simpa [prefixWord, tailWord_5173823, baseEnd_5173823] using wordTrace_append hprefix tailTrace_5173823
  have hstable : (prefixWord ++ tailWord_5173823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173823).length < 2 ^ (prefixWord ++ tailWord_5173823).sum := by decide
  have hdescent : baseEnd_5173823 < baseStart_5173823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173830 : List Nat := [6, 1, 1, 1, 2, 1, 2, 9]
def baseStart_5173830 : Nat := 118140960795 + 5173830 * 2 ^ 59
def prefixEnd_5173830 : Nat := 4983230072969 + 3 ^ 40 * 5173830 * 2
def baseEnd_5173830 : Nat := 98394874616725837038185

theorem tailTrace_5173830 : CollatzResearch.WordTrace tailWord_5173830 prefixEnd_5173830 98394874616725837038185 := by
  unfold tailWord_5173830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5897033838940781395641967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125803388564070003107028629 5897033838940781395641967)
  ·
    refine ⟨8845550758411172093462951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5897033838940781395641967 8845550758411172093462951)
    ·
      refine ⟨13268326137616758140194427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8845550758411172093462951 13268326137616758140194427)
      ·
        refine ⟨19902489206425137210291641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13268326137616758140194427 19902489206425137210291641)
        ·
          refine ⟨14926866904818852907718731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19902489206425137210291641 14926866904818852907718731)
          ·
            refine ⟨22390300357228279361578097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14926866904818852907718731 22390300357228279361578097)
            ·
              refine ⟨16792725267921209521183573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22390300357228279361578097 16792725267921209521183573)
              ·
                refine ⟨98394874616725837038185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16792725267921209521183573 98394874616725837038185)
                ·
                  rfl

theorem cell23_5173830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_5173830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173830 prefixEnd_5173830 := by exact prefixLift 5173830
  have htrace : WordTrace (prefixWord ++ tailWord_5173830) baseStart_5173830 baseEnd_5173830 := by
    simpa [prefixWord, tailWord_5173830, baseEnd_5173830] using wordTrace_append hprefix tailTrace_5173830
  have hstable : (prefixWord ++ tailWord_5173830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173830).length < 2 ^ (prefixWord ++ tailWord_5173830).sum := by decide
  have hdescent : baseEnd_5173830 < baseStart_5173830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173857 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_5173857 : Nat := 118140960795 + 5173857 * 2 ^ 59
def prefixEnd_5173857 : Nat := 4983230072969 + 3 ^ 40 * 5173857 * 2
def baseEnd_5173857 : Nat := 2656675478629268994393371

theorem tailTrace_5173857 : CollatzResearch.WordTrace tailWord_5173857 prefixEnd_5173857 2656675478629268994393371 := by
  unfold tailWord_5173857
  simp only [CollatzResearch.WordTrace]
  refine ⟨188706067617007188271775825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125804045078004792181183883 188706067617007188271775825)
  ·
    refine ⟨141529550712755391203831869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188706067617007188271775825 141529550712755391203831869)
    ·
      refine ⟨53073581517283271701436951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141529550712755391203831869 53073581517283271701436951)
      ·
        refine ⟨79610372275924907552155427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53073581517283271701436951 79610372275924907552155427)
        ·
          refine ⟨119415558413887361328233141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79610372275924907552155427 119415558413887361328233141)
          ·
            refine ⟨11195208601301940124521857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119415558413887361328233141 11195208601301940124521857)
            ·
              refine ⟨8396406450976455093391393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11195208601301940124521857 8396406450976455093391393)
              ·
                refine ⟨6297304838232341320043545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8396406450976455093391393 6297304838232341320043545)
                ·
                  refine ⟨4722978628674255990032659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6297304838232341320043545 4722978628674255990032659)
                  ·
                    refine ⟨7084467943011383985048989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4722978628674255990032659 7084467943011383985048989)
                    ·
                      refine ⟨2656675478629268994393371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7084467943011383985048989 2656675478629268994393371)
                      ·
                        rfl

theorem cell23_5173857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_5173857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173857 prefixEnd_5173857 := by exact prefixLift 5173857
  have htrace : WordTrace (prefixWord ++ tailWord_5173857) baseStart_5173857 baseEnd_5173857 := by
    simpa [prefixWord, tailWord_5173857, baseEnd_5173857] using wordTrace_append hprefix tailTrace_5173857
  have hstable : (prefixWord ++ tailWord_5173857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173857).length < 2 ^ (prefixWord ++ tailWord_5173857).sum := by decide
  have hdescent : baseEnd_5173857 < baseStart_5173857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173858 : List Nat := [3, 3, 2, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5173858 : Nat := 118140960795 + 5173858 * 2 ^ 59
def prefixEnd_5173858 : Nat := 4983230072969 + 3 ^ 40 * 5173858 * 2
def baseEnd_5173858 : Nat := 2656675992109923490480867

theorem tailTrace_5173858 : CollatzResearch.WordTrace tailWord_5173858 prefixEnd_5173858 2656675992109923490480867 := by
  unfold tailWord_5173858
  simp only [CollatzResearch.WordTrace]
  refine ⟨47176526022500891360640557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125804069393335710295041485 47176526022500891360640557)
  ·
    refine ⟨17691197258437834260240209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47176526022500891360640557 17691197258437834260240209)
    ·
      refine ⟨13268397943828375695180157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17691197258437834260240209 13268397943828375695180157)
      ·
        refine ⟨4975649228935640885692559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13268397943828375695180157 4975649228935640885692559)
        ·
          refine ⟨7463473843403461328538839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4975649228935640885692559 7463473843403461328538839)
          ·
            refine ⟨11195210765105191992808259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463473843403461328538839 11195210765105191992808259)
            ·
              refine ⟨16792816147657787989212389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11195210765105191992808259 16792816147657787989212389)
              ·
                refine ⟨3148653027685835247977323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16792816147657787989212389 3148653027685835247977323)
                ·
                  refine ⟨4722979541528752871965985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3148653027685835247977323 4722979541528752871965985)
                  ·
                    refine ⟨3542234656146564653974489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4722979541528752871965985 3542234656146564653974489)
                    ·
                      refine ⟨2656675992109923490480867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3542234656146564653974489 2656675992109923490480867)
                      ·
                        rfl

theorem cell23_5173858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5173858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173858 prefixEnd_5173858 := by exact prefixLift 5173858
  have htrace : WordTrace (prefixWord ++ tailWord_5173858) baseStart_5173858 baseEnd_5173858 := by
    simpa [prefixWord, tailWord_5173858, baseEnd_5173858] using wordTrace_append hprefix tailTrace_5173858
  have hstable : (prefixWord ++ tailWord_5173858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173858).length < 2 ^ (prefixWord ++ tailWord_5173858).sum := by decide
  have hdescent : baseEnd_5173858 < baseStart_5173858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173913 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 3]
def baseStart_5173913 : Nat := 118140960795 + 5173913 * 2 ^ 59
def prefixEnd_5173913 : Nat := 4983230072969 + 3 ^ 40 * 5173913 * 2
def baseEnd_5173913 : Nat := 2656704233545920775293113

theorem tailTrace_5173913 : CollatzResearch.WordTrace tailWord_5173913 prefixEnd_5173913 2656704233545920775293113 := by
  unfold tailWord_5173913
  simp only [CollatzResearch.WordTrace]
  refine ⟨188708110104804309835814393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125805406736536206557209595 188708110104804309835814393)
  ·
    refine ⟨141531082578603232376860795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188708110104804309835814393 141531082578603232376860795)
    ·
      refine ⟨212296623867904848565291193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141531082578603232376860795 212296623867904848565291193)
      ·
        refine ⟨159222467900928636423968395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212296623867904848565291193 159222467900928636423968395)
        ·
          refine ⟨238833701851392954635952593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159222467900928636423968395 238833701851392954635952593)
          ·
            refine ⟨179125276388544715976964445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238833701851392954635952593 179125276388544715976964445)
            ·
              refine ⟨67171978645704268491361667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179125276388544715976964445 67171978645704268491361667)
              ·
                refine ⟨100757967968556402737042501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67171978645704268491361667 100757967968556402737042501)
                ·
                  refine ⟨18892118994104325513195469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100757967968556402737042501 18892118994104325513195469)
                  ·
                    refine ⟨7084544622789122067448301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18892118994104325513195469 7084544622789122067448301)
                    ·
                      refine ⟨2656704233545920775293113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7084544622789122067448301 2656704233545920775293113)
                      ·
                        rfl

theorem cell23_5173913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_5173913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173913 prefixEnd_5173913 := by exact prefixLift 5173913
  have htrace : WordTrace (prefixWord ++ tailWord_5173913) baseStart_5173913 baseEnd_5173913 := by
    simpa [prefixWord, tailWord_5173913, baseEnd_5173913] using wordTrace_append hprefix tailTrace_5173913
  have hstable : (prefixWord ++ tailWord_5173913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173913).length < 2 ^ (prefixWord ++ tailWord_5173913).sum := by decide
  have hdescent : baseEnd_5173913 < baseStart_5173913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173920 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 7]
def baseStart_5173920 : Nat := 118140960795 + 5173920 * 2 ^ 59
def prefixEnd_5173920 : Nat := 4983230072969 + 3 ^ 40 * 5173920 * 2
def baseEnd_5173920 : Nat := 295189758656722471989509

theorem tailTrace_5173920 : CollatzResearch.WordTrace tailWord_5173920 prefixEnd_5173920 295189758656722471989509 := by
  unfold tailWord_5173920
  simp only [CollatzResearch.WordTrace]
  refine ⟨94354182707889475015659607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125805576943852633354212809 94354182707889475015659607)
  ·
    refine ⟨141531274061834212523489411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94354182707889475015659607 141531274061834212523489411)
    ·
      refine ⟨212296911092751318785234117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141531274061834212523489411 212296911092751318785234117)
      ·
        refine ⟨39805670829890872272231397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212296911092751318785234117 39805670829890872272231397)
        ·
          refine ⟨7463563280604538551043387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39805670829890872272231397 7463563280604538551043387)
          ·
            refine ⟨11195344920906807826565081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463563280604538551043387 11195344920906807826565081)
            ·
              refine ⟨8396508690680105869923811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11195344920906807826565081 8396508690680105869923811)
              ·
                refine ⟨12594763036020158804885717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8396508690680105869923811 12594763036020158804885717)
                ·
                  refine ⟨295189758656722471989509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12594763036020158804885717 295189758656722471989509)
                  ·
                    rfl

theorem cell23_5173920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 7].length) (baseStart_5173920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173920 prefixEnd_5173920 := by exact prefixLift 5173920
  have htrace : WordTrace (prefixWord ++ tailWord_5173920) baseStart_5173920 baseEnd_5173920 := by
    simpa [prefixWord, tailWord_5173920, baseEnd_5173920] using wordTrace_append hprefix tailTrace_5173920
  have hstable : (prefixWord ++ tailWord_5173920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173920).length < 2 ^ (prefixWord ++ tailWord_5173920).sum := by decide
  have hdescent : baseEnd_5173920 < baseStart_5173920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5173950 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_5173950 : Nat := 118140960795 + 5173950 * 2 ^ 59
def prefixEnd_5173950 : Nat := 4983230072969 + 3 ^ 40 * 5173950 * 2
def baseEnd_5173950 : Nat := 885574410776712376843481

theorem tailTrace_5173950 : CollatzResearch.WordTrace tailWord_5173950 prefixEnd_5173950 885574410776712376843481 := by
  unfold tailWord_5173950
  simp only [CollatzResearch.WordTrace]
  refine ⟨23588682450708783144363913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125806306403780176769940869 23588682450708783144363913)
  ·
    refine ⟨17691511838031587358272935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23588682450708783144363913 17691511838031587358272935)
    ·
      refine ⟨26537267757047381037409403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17691511838031587358272935 26537267757047381037409403)
      ·
        refine ⟨39805901635571071556114105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26537267757047381037409403 39805901635571071556114105)
        ·
          refine ⟨29854426226678303667085579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39805901635571071556114105 29854426226678303667085579)
          ·
            refine ⟨44781639340017455500628369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29854426226678303667085579 44781639340017455500628369)
            ·
              refine ⟨33586229505013091625471277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44781639340017455500628369 33586229505013091625471277)
              ·
                refine ⟨12594836064379909359551729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33586229505013091625471277 12594836064379909359551729)
                ·
                  refine ⟨9446127048284932019663797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12594836064379909359551729 9446127048284932019663797)
                  ·
                    refine ⟨885574410776712376843481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9446127048284932019663797 885574410776712376843481)
                    ·
                      rfl

theorem cell23_5173950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_5173950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5173950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5173950 prefixEnd_5173950 := by exact prefixLift 5173950
  have htrace : WordTrace (prefixWord ++ tailWord_5173950) baseStart_5173950 baseEnd_5173950 := by
    simpa [prefixWord, tailWord_5173950, baseEnd_5173950] using wordTrace_append hprefix tailTrace_5173950
  have hstable : (prefixWord ++ tailWord_5173950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5173950).length < 2 ^ (prefixWord ++ tailWord_5173950).sum := by decide
  have hdescent : baseEnd_5173950 < baseStart_5173950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5173950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174037 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_5174037 : Nat := 118140960795 + 5174037 * 2 ^ 59
def prefixEnd_5174037 : Nat := 4983230072969 + 3 ^ 40 * 5174037 * 2
def baseEnd_5174037 : Nat := 2656767905147078290142543

theorem tailTrace_5174037 : CollatzResearch.WordTrace tailWord_5174037 prefixEnd_5174037 2656767905147078290142543 := by
  unfold tailWord_5174037
  simp only [CollatzResearch.WordTrace]
  refine ⟨188712632756355079013328365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125808421837570052675552243 188712632756355079013328365)
  ·
    refine ⟨70767237283633154629998137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188712632756355079013328365 70767237283633154629998137)
    ·
      refine ⟨53075427962724865972498603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70767237283633154629998137 53075427962724865972498603)
      ·
        refine ⟨79613141944087298958747905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53075427962724865972498603 79613141944087298958747905)
        ·
          refine ⟨59709856458065474219060929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79613141944087298958747905 59709856458065474219060929)
          ·
            refine ⟨44782392343549105664295697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59709856458065474219060929 44782392343549105664295697)
            ·
              refine ⟨33586794257661829248221773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44782392343549105664295697 33586794257661829248221773)
              ·
                refine ⟨12595047846623185968083165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33586794257661829248221773 12595047846623185968083165)
                ·
                  refine ⟨4723142942483694738031187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12595047846623185968083165 4723142942483694738031187)
                  ·
                    refine ⟨7084714413725542107046781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4723142942483694738031187 7084714413725542107046781)
                    ·
                      refine ⟨2656767905147078290142543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7084714413725542107046781 2656767905147078290142543)
                      ·
                        rfl

theorem cell23_5174037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_5174037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174037 prefixEnd_5174037 := by exact prefixLift 5174037
  have htrace : WordTrace (prefixWord ++ tailWord_5174037) baseStart_5174037 baseEnd_5174037 := by
    simpa [prefixWord, tailWord_5174037, baseEnd_5174037] using wordTrace_append hprefix tailTrace_5174037
  have hstable : (prefixWord ++ tailWord_5174037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174037).length < 2 ^ (prefixWord ++ tailWord_5174037).sum := by decide
  have hdescent : baseEnd_5174037 < baseStart_5174037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174043 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 4]
def baseStart_5174043 : Nat := 118140960795 + 5174043 * 2 ^ 59
def prefixEnd_5174043 : Nat := 4983230072969 + 3 ^ 40 * 5174043 * 2
def baseEnd_5174043 : Nat := 2656770986031005266667515

theorem tailTrace_5174043 : CollatzResearch.WordTrace tailWord_5174043 prefixEnd_5174043 2656770986031005266667515 := by
  unfold tailWord_5174043
  simp only [CollatzResearch.WordTrace]
  refine ⟨188712851594333342038046783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125808567729555561358697855 188712851594333342038046783)
  ·
    refine ⟨283069277391500013057070175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188712851594333342038046783 283069277391500013057070175)
    ·
      refine ⟨424603916087250019585605263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283069277391500013057070175 424603916087250019585605263)
      ·
        refine ⟨636905874130875029378407895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424603916087250019585605263 636905874130875029378407895)
        ·
          refine ⟨955358811196312544067611843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636905874130875029378407895 955358811196312544067611843)
          ·
            refine ⟨1433038216794468816101417765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955358811196312544067611843 1433038216794468816101417765)
            ·
              refine ⟨268694665648962903019015831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1433038216794468816101417765 268694665648962903019015831)
              ·
                refine ⟨403041998473444354528523747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268694665648962903019015831 403041998473444354528523747)
                ·
                  refine ⟨604562997710166531792785621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403041998473444354528523747 604562997710166531792785621)
                  ·
                    refine ⟨14169445258832028088893413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 604562997710166531792785621 14169445258832028088893413)
                    ·
                      refine ⟨2656770986031005266667515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14169445258832028088893413 2656770986031005266667515)
                      ·
                        rfl

theorem cell23_5174043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 4].length) (baseStart_5174043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174043 prefixEnd_5174043 := by exact prefixLift 5174043
  have htrace : WordTrace (prefixWord ++ tailWord_5174043) baseStart_5174043 baseEnd_5174043 := by
    simpa [prefixWord, tailWord_5174043, baseEnd_5174043] using wordTrace_append hprefix tailTrace_5174043
  have hstable : (prefixWord ++ tailWord_5174043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174043).length < 2 ^ (prefixWord ++ tailWord_5174043).sum := by decide
  have hdescent : baseEnd_5174043 < baseStart_5174043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174058 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5174058 : Nat := 118140960795 + 5174058 * 2 ^ 59
def prefixEnd_5174058 : Nat := 4983230072969 + 3 ^ 40 * 5174058 * 2
def baseEnd_5174058 : Nat := 2656778688240822707979947

theorem tailTrace_5174058 : CollatzResearch.WordTrace tailWord_5174058 prefixEnd_5174058 2656778688240822707979947 := by
  unfold tailWord_5174058
  simp only [CollatzResearch.WordTrace]
  refine ⟨47178349672319749899960707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125808932459519333066561885 47178349672319749899960707)
  ·
    refine ⟨70767524508479624849941061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47178349672319749899960707 70767524508479624849941061)
    ·
      refine ⟨13268910845339929659363949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70767524508479624849941061 13268910845339929659363949)
      ·
        refine ⟨4975841567002473622261481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13268910845339929659363949 4975841567002473622261481)
        ·
          refine ⟨3731881175251855216696111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4975841567002473622261481 3731881175251855216696111)
          ·
            refine ⟨5597821762877782825044167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3731881175251855216696111 5597821762877782825044167)
            ·
              refine ⟨8396732644316674237566251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5597821762877782825044167 8396732644316674237566251)
              ·
                refine ⟨12595098966475011356349377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8396732644316674237566251 12595098966475011356349377)
                ·
                  refine ⟨9446324224856258517262033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12595098966475011356349377 9446324224856258517262033)
                  ·
                    refine ⟨7084743168642193887946525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9446324224856258517262033 7084743168642193887946525)
                    ·
                      refine ⟨2656778688240822707979947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7084743168642193887946525 2656778688240822707979947)
                      ·
                        rfl

theorem cell23_5174058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5174058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174058 prefixEnd_5174058 := by exact prefixLift 5174058
  have htrace : WordTrace (prefixWord ++ tailWord_5174058) baseStart_5174058 baseEnd_5174058 := by
    simpa [prefixWord, tailWord_5174058, baseEnd_5174058] using wordTrace_append hprefix tailTrace_5174058
  have hstable : (prefixWord ++ tailWord_5174058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174058).length < 2 ^ (prefixWord ++ tailWord_5174058).sum := by decide
  have hdescent : baseEnd_5174058 < baseStart_5174058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174060 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 4]
def baseStart_5174060 : Nat := 118140960795 + 5174060 * 2 ^ 59
def prefixEnd_5174060 : Nat := 4983230072969 + 3 ^ 40 * 5174060 * 2
def baseEnd_5174060 : Nat := 2656779715202131700154937

theorem tailTrace_5174060 : CollatzResearch.WordTrace tailWord_5174060 prefixEnd_5174060 2656779715202131700154937 := by
  unfold tailWord_5174060
  simp only [CollatzResearch.WordTrace]
  refine ⟨94356735817635876970707817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125808981090181169294277089 94356735817635876970707817)
  ·
    refine ⟨70767551863226907728030863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94356735817635876970707817 70767551863226907728030863)
    ·
      refine ⟨106151327794840361592046295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70767551863226907728030863 106151327794840361592046295)
      ·
        refine ⟨159226991692260542388069443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106151327794840361592046295 159226991692260542388069443)
        ·
          refine ⟨238840487538390813582104165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159226991692260542388069443 238840487538390813582104165)
          ·
            refine ⟨44782591413448277546644531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238840487538390813582104165 44782591413448277546644531)
            ·
              refine ⟨67173887120172416319966797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44782591413448277546644531 67173887120172416319966797)
              ·
                refine ⟨25190207670064656119987549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67173887120172416319966797 25190207670064656119987549)
                ·
                  refine ⟨9446327876274246044995331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25190207670064656119987549 9446327876274246044995331)
                  ·
                    refine ⟨14169491814411369067492997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9446327876274246044995331 14169491814411369067492997)
                    ·
                      refine ⟨2656779715202131700154937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14169491814411369067492997 2656779715202131700154937)
                      ·
                        rfl

theorem cell23_5174060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_5174060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174060 prefixEnd_5174060 := by exact prefixLift 5174060
  have htrace : WordTrace (prefixWord ++ tailWord_5174060) baseStart_5174060 baseEnd_5174060 := by
    simpa [prefixWord, tailWord_5174060, baseEnd_5174060] using wordTrace_append hprefix tailTrace_5174060
  have hstable : (prefixWord ++ tailWord_5174060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174060).length < 2 ^ (prefixWord ++ tailWord_5174060).sum := by decide
  have hdescent : baseEnd_5174060 < baseStart_5174060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174063 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_5174063 : Nat := 118140960795 + 5174063 * 2 ^ 59
def prefixEnd_5174063 : Nat := 4983230072969 + 3 ^ 40 * 5174063 * 2
def baseEnd_5174063 : Nat := 2656781255644095188417423

theorem tailTrace_5174063 : CollatzResearch.WordTrace tailWord_5174063 prefixEnd_5174063 2656781255644095188417423 := by
  unfold tailWord_5174063
  simp only [CollatzResearch.WordTrace]
  refine ⟨188713581054260885453774843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125809054036173923635849895 188713581054260885453774843)
  ·
    refine ⟨283070371581391328180662265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188713581054260885453774843 283070371581391328180662265)
    ·
      refine ⟨212302778686043496135496699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283070371581391328180662265 212302778686043496135496699)
      ·
        refine ⟨318454168029065244203245049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212302778686043496135496699 318454168029065244203245049)
        ·
          refine ⟨238840626021798933152433787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318454168029065244203245049 238840626021798933152433787)
          ·
            refine ⟨358260939032698399728650681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238840626021798933152433787 358260939032698399728650681)
            ·
              refine ⟨268695704274523799796488011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358260939032698399728650681 268695704274523799796488011)
              ·
                refine ⟨403043556411785699694732017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268695704274523799796488011 403043556411785699694732017)
                ·
                  refine ⟨302282667308839274771049013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 403043556411785699694732017 302282667308839274771049013)
                  ·
                    refine ⟨28339000060203682009785845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 302282667308839274771049013 28339000060203682009785845)
                    ·
                      refine ⟨2656781255644095188417423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28339000060203682009785845 2656781255644095188417423)
                      ·
                        rfl

theorem cell23_5174063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_5174063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174063 prefixEnd_5174063 := by exact prefixLift 5174063
  have htrace : WordTrace (prefixWord ++ tailWord_5174063) baseStart_5174063 baseEnd_5174063 := by
    simpa [prefixWord, tailWord_5174063, baseEnd_5174063] using wordTrace_append hprefix tailTrace_5174063
  have hstable : (prefixWord ++ tailWord_5174063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174063).length < 2 ^ (prefixWord ++ tailWord_5174063).sum := by decide
  have hdescent : baseEnd_5174063 < baseStart_5174063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174083 : List Nat := [1, 1, 1, 3, 1, 4, 12]
def baseStart_5174083 : Nat := 118140960795 + 5174083 * 2 ^ 59
def prefixEnd_5174083 : Nat := 4983230072969 + 3 ^ 40 * 5174083 * 2
def baseEnd_5174083 : Nat := 32799895373545495187251

theorem tailTrace_5174083 : CollatzResearch.WordTrace tailWord_5174083 prefixEnd_5174083 32799895373545495187251 := by
  unfold tailWord_5174083
  simp only [CollatzResearch.WordTrace]
  refine ⟨188714310514188428869502903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125809540342792285913001935 188714310514188428869502903)
  ·
    refine ⟨283071465771282643304254355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188714310514188428869502903 283071465771282643304254355)
    ·
      refine ⟨424607198656923964956381533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283071465771282643304254355 424607198656923964956381533)
      ·
        refine ⟨159227699496346486858643075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424607198656923964956381533 159227699496346486858643075)
        ·
          refine ⟨238841549244519730287964613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159227699496346486858643075 238841549244519730287964613)
          ·
            refine ⟨44782790483347449428993365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 238841549244519730287964613 44782790483347449428993365)
            ·
              refine ⟨32799895373545495187251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 44782790483347449428993365 32799895373545495187251)
              ·
                rfl

theorem cell23_5174083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 12].length) (baseStart_5174083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174083 prefixEnd_5174083 := by exact prefixLift 5174083
  have htrace : WordTrace (prefixWord ++ tailWord_5174083) baseStart_5174083 baseEnd_5174083 := by
    simpa [prefixWord, tailWord_5174083, baseEnd_5174083] using wordTrace_append hprefix tailTrace_5174083
  have hstable : (prefixWord ++ tailWord_5174083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174083).length < 2 ^ (prefixWord ++ tailWord_5174083).sum := by decide
  have hdescent : baseEnd_5174083 < baseStart_5174083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174097 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 5]
def baseStart_5174097 : Nat := 118140960795 + 5174097 * 2 ^ 59
def prefixEnd_5174097 : Nat := 4983230072969 + 3 ^ 40 * 5174097 * 2
def baseEnd_5174097 : Nat := 2656798713986348055392267

theorem tailTrace_5174097 : CollatzResearch.WordTrace tailWord_5174097 prefixEnd_5174097 2656798713986348055392267 := by
  unfold tailWord_5174097
  simp only [CollatzResearch.WordTrace]
  refine ⟨188714821136137709260512545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125809880757425139507008363 188714821136137709260512545)
  ·
    refine ⟨141536115852103281945384409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188714821136137709260512545 141536115852103281945384409)
    ·
      refine ⟨106152086889077461459038307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141536115852103281945384409 106152086889077461459038307)
      ·
        refine ⟨159228130333616192188557461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106152086889077461459038307 159228130333616192188557461)
        ·
          refine ⟨7463818609388259008838631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159228130333616192188557461 7463818609388259008838631)
          ·
            refine ⟨11195727914082388513257947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7463818609388259008838631 11195727914082388513257947)
            ·
              refine ⟨16793591871123582769886921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11195727914082388513257947 16793591871123582769886921)
              ·
                refine ⟨12595193903342687077415191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16793591871123582769886921 12595193903342687077415191)
                ·
                  refine ⟨18892790855014030616122787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12595193903342687077415191 18892790855014030616122787)
                  ·
                    refine ⟨28339186282521045924184181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18892790855014030616122787 28339186282521045924184181)
                    ·
                      refine ⟨2656798713986348055392267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28339186282521045924184181 2656798713986348055392267)
                      ·
                        rfl

theorem cell23_5174097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 1, 5].length) (baseStart_5174097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174097 prefixEnd_5174097 := by exact prefixLift 5174097
  have htrace : WordTrace (prefixWord ++ tailWord_5174097) baseStart_5174097 baseEnd_5174097 := by
    simpa [prefixWord, tailWord_5174097, baseEnd_5174097] using wordTrace_append hprefix tailTrace_5174097
  have hstable : (prefixWord ++ tailWord_5174097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174097).length < 2 ^ (prefixWord ++ tailWord_5174097).sum := by decide
  have hdescent : baseEnd_5174097 < baseStart_5174097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174197 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_5174197 : Nat := 118140960795 + 5174197 * 2 ^ 59
def prefixEnd_5174197 : Nat := 4983230072969 + 3 ^ 40 * 5174197 * 2
def baseEnd_5174197 : Nat := 2656850062051797664141807

theorem tailTrace_5174197 : CollatzResearch.WordTrace tailWord_5174197 prefixEnd_5174197 2656850062051797664141807 := by
  unfold tailWord_5174197
  simp only [CollatzResearch.WordTrace]
  refine ⟨188718468435775426339152845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125812312290516950892768563 188718468435775426339152845)
  ·
    refine ⟨70769425663415784877182317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188718468435775426339152845 70769425663415784877182317)
    ·
      refine ⟨26538534623780919328943369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70769425663415784877182317 26538534623780919328943369)
      ·
        refine ⟨19903900967835689496707527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26538534623780919328943369 19903900967835689496707527)
        ·
          refine ⟨29855851451753534245061291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19903900967835689496707527 29855851451753534245061291)
          ·
            refine ⟨44783777177630301367591937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29855851451753534245061291 44783777177630301367591937)
            ·
              refine ⟨33587832883222726025693953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44783777177630301367591937 33587832883222726025693953)
              ·
                refine ⟨25190874662417044519270465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33587832883222726025693953 25190874662417044519270465)
                ·
                  refine ⟨18893155996812783389452849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25190874662417044519270465 18893155996812783389452849)
                  ·
                    refine ⟨14169866997609587542089637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18893155996812783389452849 14169866997609587542089637)
                    ·
                      refine ⟨2656850062051797664141807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14169866997609587542089637 2656850062051797664141807)
                      ·
                        rfl

theorem cell23_5174197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_5174197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174197 prefixEnd_5174197 := by exact prefixLift 5174197
  have htrace : WordTrace (prefixWord ++ tailWord_5174197) baseStart_5174197 baseEnd_5174197 := by
    simpa [prefixWord, tailWord_5174197, baseEnd_5174197] using wordTrace_append hprefix tailTrace_5174197
  have hstable : (prefixWord ++ tailWord_5174197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174197).length < 2 ^ (prefixWord ++ tailWord_5174197).sum := by decide
  have hdescent : baseEnd_5174197 < baseStart_5174197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174201 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 2, 2, 2]
def baseStart_5174201 : Nat := 118140960795 + 5174201 * 2 ^ 59
def prefixEnd_5174201 : Nat := 4983230072969 + 3 ^ 40 * 5174201 * 2
def baseEnd_5174201 : Nat := 2656852115974415648491789

theorem tailTrace_5174201 : CollatzResearch.WordTrace tailWord_5174201 prefixEnd_5174201 2656852115974415648491789 := by
  unfold tailWord_5174201
  simp only [CollatzResearch.WordTrace]
  refine ⟨188718614327760935022298457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125812409551840623348198971 188718614327760935022298457)
  ·
    refine ⟨141538960745820701266723843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188718614327760935022298457 141538960745820701266723843)
    ·
      refine ⟨212308441118731051900085765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141538960745820701266723843 212308441118731051900085765)
      ·
        refine ⟨39807832709762072231266081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212308441118731051900085765 39807832709762072231266081)
        ·
          refine ⟨29855874532321554173449561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39807832709762072231266081 29855874532321554173449561)
          ·
            refine ⟨22391905899241165630087171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29855874532321554173449561 22391905899241165630087171)
            ·
              refine ⟨33587858848861748445130757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22391905899241165630087171 33587858848861748445130757)
              ·
                refine ⟨6297723534161577833462017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33587858848861748445130757 6297723534161577833462017)
                ·
                  refine ⟨4723292650621183375096513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6297723534161577833462017 4723292650621183375096513)
                  ·
                    refine ⟨3542469487965887531322385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4723292650621183375096513 3542469487965887531322385)
                    ·
                      refine ⟨2656852115974415648491789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3542469487965887531322385 2656852115974415648491789)
                      ·
                        rfl

theorem cell23_5174201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_5174201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174201 prefixEnd_5174201 := by exact prefixLift 5174201
  have htrace : WordTrace (prefixWord ++ tailWord_5174201) baseStart_5174201 baseEnd_5174201 := by
    simpa [prefixWord, tailWord_5174201, baseEnd_5174201] using wordTrace_append hprefix tailTrace_5174201
  have hstable : (prefixWord ++ tailWord_5174201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174201).length < 2 ^ (prefixWord ++ tailWord_5174201).sum := by decide
  have hdescent : baseEnd_5174201 < baseStart_5174201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174277 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 3]
def baseStart_5174277 : Nat := 118140960795 + 5174277 * 2 ^ 59
def prefixEnd_5174277 : Nat := 4983230072969 + 3 ^ 40 * 5174277 * 2
def baseEnd_5174277 : Nat := 2656891140504157351141439

theorem tailTrace_5174277 : CollatzResearch.WordTrace tailWord_5174277 prefixEnd_5174277 2656891140504157351141439 := by
  unfold tailWord_5174277
  simp only [CollatzResearch.WordTrace]
  refine ⟨188721386275485600002065085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125814257516990400001376723 188721386275485600002065085)
  ·
    refine ⟨70770519853307100000774407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188721386275485600002065085 70770519853307100000774407)
    ·
      refine ⟨106155779779960650001161611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70770519853307100000774407 106155779779960650001161611)
      ·
        refine ⟨159233669669940975001742417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106155779779960650001161611 159233669669940975001742417)
        ·
          refine ⟨119425252252455731251306813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159233669669940975001742417 119425252252455731251306813)
          ·
            refine ⟨44784469594670899219240055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119425252252455731251306813 44784469594670899219240055)
            ·
              refine ⟨67176704392006348828860083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44784469594670899219240055 67176704392006348828860083)
              ·
                refine ⟨100765056588009523243290125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67176704392006348828860083 100765056588009523243290125)
                ·
                  refine ⟨37786896220503571216233797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100765056588009523243290125 37786896220503571216233797)
                  ·
                    refine ⟨7085043041344419603043837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37786896220503571216233797 7085043041344419603043837)
                    ·
                      refine ⟨2656891140504157351141439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085043041344419603043837 2656891140504157351141439)
                      ·
                        rfl

theorem cell23_5174277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 4, 3].length) (baseStart_5174277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174277 prefixEnd_5174277 := by exact prefixLift 5174277
  have htrace : WordTrace (prefixWord ++ tailWord_5174277) baseStart_5174277 baseEnd_5174277 := by
    simpa [prefixWord, tailWord_5174277, baseEnd_5174277] using wordTrace_append hprefix tailTrace_5174277
  have hstable : (prefixWord ++ tailWord_5174277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174277).length < 2 ^ (prefixWord ++ tailWord_5174277).sum := by decide
  have hdescent : baseEnd_5174277 < baseStart_5174277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174284 : List Nat := [2, 2, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_5174284 : Nat := 118140960795 + 5174284 * 2 ^ 59
def prefixEnd_5174284 : Nat := 4983230072969 + 3 ^ 40 * 5174284 * 2
def baseEnd_5174284 : Nat := 885631578289579607917969

theorem tailTrace_5174284 : CollatzResearch.WordTrace tailWord_5174284 prefixEnd_5174284 885631578289579607917969 := by
  unfold tailWord_5174284
  simp only [CollatzResearch.WordTrace]
  refine ⟨94360820793230120098784953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125814427724306826798379937 94360820793230120098784953)
  ·
    refine ⟨70770615594922590074088715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94360820793230120098784953 70770615594922590074088715)
    ·
      refine ⟨106155923392383885111133073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70770615594922590074088715 106155923392383885111133073)
      ·
        refine ⟨79616942544287913833349805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106155923392383885111133073 79616942544287913833349805)
        ·
          refine ⟨29856353454107967687506177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79616942544287913833349805 29856353454107967687506177)
          ·
            refine ⟨22392265090580975765629633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29856353454107967687506177 22392265090580975765629633)
            ·
              refine ⟨16794198817935731824222225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22392265090580975765629633 16794198817935731824222225)
              ·
                refine ⟨12595649113451798868166669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16794198817935731824222225 12595649113451798868166669)
                ·
                  refine ⟨4723368417544424575562501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12595649113451798868166669 4723368417544424575562501)
                  ·
                    refine ⟨885631578289579607917969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4723368417544424575562501 885631578289579607917969)
                    ·
                      rfl

theorem cell23_5174284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_5174284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174284 prefixEnd_5174284 := by exact prefixLift 5174284
  have htrace : WordTrace (prefixWord ++ tailWord_5174284) baseStart_5174284 baseEnd_5174284 := by
    simpa [prefixWord, tailWord_5174284, baseEnd_5174284] using wordTrace_append hprefix tailTrace_5174284
  have hstable : (prefixWord ++ tailWord_5174284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174284).length < 2 ^ (prefixWord ++ tailWord_5174284).sum := by decide
  have hdescent : baseEnd_5174284 < baseStart_5174284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174311 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_5174311 : Nat := 118140960795 + 5174311 * 2 ^ 59
def prefixEnd_5174311 : Nat := 4983230072969 + 3 ^ 40 * 5174311 * 2
def baseEnd_5174311 : Nat := 2656908598846410218116283

theorem tailTrace_5174311 : CollatzResearch.WordTrace tailWord_5174311 prefixEnd_5174311 2656908598846410218116283 := by
  unfold tailWord_5174311
  simp only [CollatzResearch.WordTrace]
  refine ⟨188722626357362423808802787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125815084238241615872535191 188722626357362423808802787)
  ·
    refine ⟨283083939536043635713204181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188722626357362423808802787 283083939536043635713204181)
    ·
      refine ⟨6634779832876022712028223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 283083939536043635713204181 6634779832876022712028223)
      ·
        refine ⟨9952169749314034068042335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6634779832876022712028223 9952169749314034068042335)
        ·
          refine ⟨14928254623971051102063503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9952169749314034068042335 14928254623971051102063503)
          ·
            refine ⟨22392381935956576653095255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14928254623971051102063503 22392381935956576653095255)
            ·
              refine ⟨33588572903934864979642883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22392381935956576653095255 33588572903934864979642883)
              ·
                refine ⟨50382859355902297469464325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33588572903934864979642883 50382859355902297469464325)
                ·
                  refine ⟨9446786129231680775524561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50382859355902297469464325 9446786129231680775524561)
                  ·
                    refine ⟨7085089596923760581643421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9446786129231680775524561 7085089596923760581643421)
                    ·
                      refine ⟨2656908598846410218116283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085089596923760581643421 2656908598846410218116283)
                      ·
                        rfl

theorem cell23_5174311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_5174311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174311 prefixEnd_5174311 := by exact prefixLift 5174311
  have htrace : WordTrace (prefixWord ++ tailWord_5174311) baseStart_5174311 baseEnd_5174311 := by
    simpa [prefixWord, tailWord_5174311, baseEnd_5174311] using wordTrace_append hprefix tailTrace_5174311
  have hstable : (prefixWord ++ tailWord_5174311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174311).length < 2 ^ (prefixWord ++ tailWord_5174311).sum := by decide
  have hdescent : baseEnd_5174311 < baseStart_5174311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174327 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 3, 5]
def baseStart_5174327 : Nat := 118140960795 + 5174327 * 2 ^ 59
def prefixEnd_5174327 : Nat := 4983230072969 + 3 ^ 40 * 5174327 * 2
def baseEnd_5174327 : Nat := 885638938178960718505403

theorem tailTrace_5174327 : CollatzResearch.WordTrace tailWord_5174327 prefixEnd_5174327 885638938178960718505403 := by
  unfold tailWord_5174327
  simp only [CollatzResearch.WordTrace]
  refine ⟨188723209925304458541385235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125815473283536305694256823 188723209925304458541385235)
  ·
    refine ⟨283084814887956687812077853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188723209925304458541385235 283084814887956687812077853)
    ·
      refine ⟨106156805582983757929529195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283084814887956687812077853 106156805582983757929529195)
      ·
        refine ⟨159235208374475636894293793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106156805582983757929529195 159235208374475636894293793)
        ·
          refine ⟨119426406280856727670720345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159235208374475636894293793 119426406280856727670720345)
          ·
            refine ⟨89569804710642545753040259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119426406280856727670720345 89569804710642545753040259)
            ·
              refine ⟨134354707065963818629560389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89569804710642545753040259 134354707065963818629560389)
              ·
                refine ⟨25191507574868215993042573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134354707065963818629560389 25191507574868215993042573)
                ·
                  refine ⟨9446815340575580997390965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25191507574868215993042573 9446815340575580997390965)
                  ·
                    refine ⟨885638938178960718505403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9446815340575580997390965 885638938178960718505403)
                    ·
                      rfl

theorem cell23_5174327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_5174327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174327 prefixEnd_5174327 := by exact prefixLift 5174327
  have htrace : WordTrace (prefixWord ++ tailWord_5174327) baseStart_5174327 baseEnd_5174327 := by
    simpa [prefixWord, tailWord_5174327, baseEnd_5174327] using wordTrace_append hprefix tailTrace_5174327
  have hstable : (prefixWord ++ tailWord_5174327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174327).length < 2 ^ (prefixWord ++ tailWord_5174327).sum := by decide
  have hdescent : baseEnd_5174327 < baseStart_5174327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174375 : List Nat := [1, 1, 5, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_5174375 : Nat := 118140960795 + 5174375 * 2 ^ 59
def prefixEnd_5174375 : Nat := 4983230072969 + 3 ^ 40 * 5174375 * 2
def baseEnd_5174375 : Nat := 2656941461608297967715989

theorem tailTrace_5174375 : CollatzResearch.WordTrace tailWord_5174375 prefixEnd_5174375 2656941461608297967715989 := by
  unfold tailWord_5174375
  simp only [CollatzResearch.WordTrace]
  refine ⟨188724960629130562739132579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125816640419420375159421719 188724960629130562739132579)
  ·
    refine ⟨283087440943695844108698869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188724960629130562739132579 283087440943695844108698869)
    ·
      refine ⟨26539447588471485385190519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 283087440943695844108698869 26539447588471485385190519)
      ·
        refine ⟨39809171382707228077785779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26539447588471485385190519 39809171382707228077785779)
        ·
          refine ⟨59713757074060842116678669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39809171382707228077785779 59713757074060842116678669)
          ·
            refine ⟨22392658902772815793754501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59713757074060842116678669 22392658902772815793754501)
            ·
              refine ⟨4198623544269902961328969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22392658902772815793754501 4198623544269902961328969)
              ·
                refine ⟨3148967658202427220996727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4198623544269902961328969 3148967658202427220996727)
                ·
                  refine ⟨4723451487303640831495091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3148967658202427220996727 4723451487303640831495091)
                  ·
                    refine ⟨7085177230955461247242637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4723451487303640831495091 7085177230955461247242637)
                    ·
                      refine ⟨2656941461608297967715989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085177230955461247242637 2656941461608297967715989)
                      ·
                        rfl

theorem cell23_5174375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_5174375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174375 prefixEnd_5174375 := by exact prefixLift 5174375
  have htrace : WordTrace (prefixWord ++ tailWord_5174375) baseStart_5174375 baseEnd_5174375 := by
    simpa [prefixWord, tailWord_5174375, baseEnd_5174375] using wordTrace_append hprefix tailTrace_5174375
  have hstable : (prefixWord ++ tailWord_5174375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174375).length < 2 ^ (prefixWord ++ tailWord_5174375).sum := by decide
  have hdescent : baseEnd_5174375 < baseStart_5174375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174384 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 3]
def baseStart_5174384 : Nat := 118140960795 + 5174384 * 2 ^ 59
def prefixEnd_5174384 : Nat := 4983230072969 + 3 ^ 40 * 5174384 * 2
def baseEnd_5174384 : Nat := 2656946082934188432503447

theorem tailTrace_5174384 : CollatzResearch.WordTrace tailWord_5174384 prefixEnd_5174384 2656946082934188432503447 := by
  unfold tailWord_5174384
  simp only [CollatzResearch.WordTrace]
  refine ⟨94362644443048978638105103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125816859257398638184140137 94362644443048978638105103)
  ·
    refine ⟨141543966664573467957157655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94362644443048978638105103 141543966664573467957157655)
    ·
      refine ⟨212315949996860201935736483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141543966664573467957157655 212315949996860201935736483)
      ·
        refine ⟨318473924995290302903604725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212315949996860201935736483 318473924995290302903604725)
        ·
          refine ⟨29856930468308465897212943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 318473924995290302903604725 29856930468308465897212943)
          ·
            refine ⟨44785395702462698845819415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29856930468308465897212943 44785395702462698845819415)
            ·
              refine ⟨67178093553694048268729123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44785395702462698845819415 67178093553694048268729123)
              ·
                refine ⟨100767140330541072403093685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67178093553694048268729123 100767140330541072403093685)
                ·
                  refine ⟨9446919405988225537790033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100767140330541072403093685 9446919405988225537790033)
                  ·
                    refine ⟨7085189554491169153342525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9446919405988225537790033 7085189554491169153342525)
                    ·
                      refine ⟨2656946082934188432503447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085189554491169153342525 2656946082934188432503447)
                      ·
                        rfl

theorem cell23_5174384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_5174384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174384 prefixEnd_5174384 := by exact prefixLift 5174384
  have htrace : WordTrace (prefixWord ++ tailWord_5174384) baseStart_5174384 baseEnd_5174384 := by
    simpa [prefixWord, tailWord_5174384, baseEnd_5174384] using wordTrace_append hprefix tailTrace_5174384
  have hstable : (prefixWord ++ tailWord_5174384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174384).length < 2 ^ (prefixWord ++ tailWord_5174384).sum := by decide
  have hdescent : baseEnd_5174384 < baseStart_5174384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174401 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_5174401 : Nat := 118140960795 + 5174401 * 2 ^ 59
def prefixEnd_5174401 : Nat := 4983230072969 + 3 ^ 40 * 5174401 * 2
def baseEnd_5174401 : Nat := 2656954812105314865990869

theorem tailTrace_5174401 : CollatzResearch.WordTrace tailWord_5174401 prefixEnd_5174401 2656954812105314865990869 := by
  unfold tailWord_5174401
  simp only [CollatzResearch.WordTrace]
  refine ⟨188725908927036369179579057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125817272618024246119719371 188725908927036369179579057)
  ·
    refine ⟨141544431695277276884684293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188725908927036369179579057 141544431695277276884684293)
    ·
      refine ⟨26539580942864489415878305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141544431695277276884684293 26539580942864489415878305)
      ·
        refine ⟨19904685707148367061908729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26539580942864489415878305 19904685707148367061908729)
        ·
          refine ⟨14928514280361275296431547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19904685707148367061908729 14928514280361275296431547)
          ·
            refine ⟨22392771420541912944647321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14928514280361275296431547 22392771420541912944647321)
            ·
              refine ⟨16794578565406434708485491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22392771420541912944647321 16794578565406434708485491)
              ·
                refine ⟨25191867848109652062728237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16794578565406434708485491 25191867848109652062728237)
                ·
                  refine ⟨9446950443041119523523089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25191867848109652062728237 9446950443041119523523089)
                  ·
                    refine ⟨7085212832280839642642317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9446950443041119523523089 7085212832280839642642317)
                    ·
                      refine ⟨2656954812105314865990869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085212832280839642642317 2656954812105314865990869)
                      ·
                        rfl

theorem cell23_5174401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_5174401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174401 prefixEnd_5174401 := by exact prefixLift 5174401
  have htrace : WordTrace (prefixWord ++ tailWord_5174401) baseStart_5174401 baseEnd_5174401 := by
    simpa [prefixWord, tailWord_5174401, baseEnd_5174401] using wordTrace_append hprefix tailTrace_5174401
  have hstable : (prefixWord ++ tailWord_5174401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174401).length < 2 ^ (prefixWord ++ tailWord_5174401).sum := by decide
  have hdescent : baseEnd_5174401 < baseStart_5174401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174418 : List Nat := [3, 2, 3, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_5174418 : Nat := 118140960795 + 5174418 * 2 ^ 59
def prefixEnd_5174418 : Nat := 4983230072969 + 3 ^ 40 * 5174418 * 2
def baseEnd_5174418 : Nat := 2656963541276441299478291

theorem tailTrace_5174418 : CollatzResearch.WordTrace tailWord_5174418 prefixEnd_5174418 2656963541276441299478291 := by
  unfold tailWord_5174418
  simp only [CollatzResearch.WordTrace]
  refine ⟨47181632241993695270736977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125817685978649854055298605 47181632241993695270736977)
  ·
    refine ⟨35386224181495271453052733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47181632241993695270736977 35386224181495271453052733)
    ·
      refine ⟨13269834068060726794894775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35386224181495271453052733 13269834068060726794894775)
      ·
        refine ⟨19904751102091090192342163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13269834068060726794894775 19904751102091090192342163)
        ·
          refine ⟨29857126653136635288513245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19904751102091090192342163 29857126653136635288513245)
          ·
            refine ⟨11196422494926238233192467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29857126653136635288513245 11196422494926238233192467)
            ·
              refine ⟨16794633742389357349788701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11196422494926238233192467 16794633742389357349788701)
              ·
                refine ⟨6297987653396009006170763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16794633742389357349788701 6297987653396009006170763)
                ·
                  refine ⟨9446981480094013509256145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6297987653396009006170763 9446981480094013509256145)
                  ·
                    refine ⟨7085236110070510131942109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9446981480094013509256145 7085236110070510131942109)
                    ·
                      refine ⟨2656963541276441299478291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085236110070510131942109 2656963541276441299478291)
                      ·
                        rfl

theorem cell23_5174418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_5174418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174418 prefixEnd_5174418 := by exact prefixLift 5174418
  have htrace : WordTrace (prefixWord ++ tailWord_5174418) baseStart_5174418 baseEnd_5174418 := by
    simpa [prefixWord, tailWord_5174418, baseEnd_5174418] using wordTrace_append hprefix tailTrace_5174418
  have hstable : (prefixWord ++ tailWord_5174418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174418).length < 2 ^ (prefixWord ++ tailWord_5174418).sum := by decide
  have hdescent : baseEnd_5174418 < baseStart_5174418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174445 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_5174445 : Nat := 118140960795 + 5174445 * 2 ^ 59
def prefixEnd_5174445 : Nat := 4983230072969 + 3 ^ 40 * 5174445 * 2
def baseEnd_5174445 : Nat := 2656977405254112693840667

theorem tailTrace_5174445 : CollatzResearch.WordTrace tailWord_5174445 prefixEnd_5174445 2656977405254112693840667 := by
  unfold tailWord_5174445
  simp only [CollatzResearch.WordTrace]
  refine ⟨188727513738876964694180789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125818342492584643129453859 188727513738876964694180789)
  ·
    refine ⟨17693204413019715440079449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188727513738876964694180789 17693204413019715440079449)
    ·
      refine ⟨13269903309764786580059587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17693204413019715440079449 13269903309764786580059587)
      ·
        refine ⟨19904854964647179870089381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13269903309764786580059587 19904854964647179870089381)
        ·
          refine ⟨3732160305871346225641759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19904854964647179870089381 3732160305871346225641759)
          ·
            refine ⟨5598240458807019338462639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3732160305871346225641759 5598240458807019338462639)
            ·
              refine ⟨8397360688210529007693959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5598240458807019338462639 8397360688210529007693959)
              ·
                refine ⟨12596041032315793511540939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8397360688210529007693959 12596041032315793511540939)
                ·
                  refine ⟨18894061548473690267311409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12596041032315793511540939 18894061548473690267311409)
                  ·
                    refine ⟨14170546161355267700483557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18894061548473690267311409 14170546161355267700483557)
                    ·
                      refine ⟨2656977405254112693840667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14170546161355267700483557 2656977405254112693840667)
                      ·
                        rfl

theorem cell23_5174445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_5174445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174445 prefixEnd_5174445 := by exact prefixLift 5174445
  have htrace : WordTrace (prefixWord ++ tailWord_5174445) baseStart_5174445 baseEnd_5174445 := by
    simpa [prefixWord, tailWord_5174445, baseEnd_5174445] using wordTrace_append hprefix tailTrace_5174445
  have hstable : (prefixWord ++ tailWord_5174445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174445).length < 2 ^ (prefixWord ++ tailWord_5174445).sum := by decide
  have hdescent : baseEnd_5174445 < baseStart_5174445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174471 : List Nat := [1, 1, 4, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_5174471 : Nat := 118140960795 + 5174471 * 2 ^ 59
def prefixEnd_5174471 : Nat := 4983230072969 + 3 ^ 40 * 5174471 * 2
def baseEnd_5174471 : Nat := 2656990755751129592115547

theorem tailTrace_5174471 : CollatzResearch.WordTrace tailWord_5174471 prefixEnd_5174471 2656990755751129592115547 := by
  unfold tailWord_5174471
  simp only [CollatzResearch.WordTrace]
  refine ⟨188728462036782771134627267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125818974691188514089751511 188728462036782771134627267)
  ·
    refine ⟨283092693055174156701940901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188728462036782771134627267 283092693055174156701940901)
    ·
      refine ⟨53079879947845154381613919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283092693055174156701940901 53079879947845154381613919)
      ·
        refine ⟨79619819921767731572420879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53079879947845154381613919 79619819921767731572420879)
        ·
          refine ⟨119429729882651597358631319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79619819921767731572420879 119429729882651597358631319)
          ·
            refine ⟨179144594823977396037946979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119429729882651597358631319 179144594823977396037946979)
            ·
              refine ⟨268716892235966094056920469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179144594823977396037946979 268716892235966094056920469)
              ·
                refine ⟨12596104323560910658918147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 268716892235966094056920469 12596104323560910658918147)
                ·
                  refine ⟨18894156485341365988377221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12596104323560910658918147 18894156485341365988377221)
                  ·
                    refine ⟨3542654341001506122820729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18894156485341365988377221 3542654341001506122820729)
                    ·
                      refine ⟨2656990755751129592115547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3542654341001506122820729 2656990755751129592115547)
                      ·
                        rfl

theorem cell23_5174471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_5174471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174471 prefixEnd_5174471 := by exact prefixLift 5174471
  have htrace : WordTrace (prefixWord ++ tailWord_5174471) baseStart_5174471 baseEnd_5174471 := by
    simpa [prefixWord, tailWord_5174471, baseEnd_5174471] using wordTrace_append hprefix tailTrace_5174471
  have hstable : (prefixWord ++ tailWord_5174471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174471).length < 2 ^ (prefixWord ++ tailWord_5174471).sum := by decide
  have hdescent : baseEnd_5174471 < baseStart_5174471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174474 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_5174474 : Nat := 118140960795 + 5174474 * 2 ^ 59
def prefixEnd_5174474 : Nat := 4983230072969 + 3 ^ 40 * 5174474 * 2
def baseEnd_5174474 : Nat := 2656992296193093080378033

theorem tailTrace_5174474 : CollatzResearch.WordTrace tailWord_5174474 prefixEnd_5174474 2656992296193093080378033 := by
  unfold tailWord_5174474
  simp only [CollatzResearch.WordTrace]
  refine ⟨47182142863942975661746619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125819047637181268431324317 47182142863942975661746619)
  ·
    refine ⟨70773214295914463492619929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47182142863942975661746619 70773214295914463492619929)
    ·
      refine ⟨53079910721935847619464947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70773214295914463492619929 53079910721935847619464947)
      ·
        refine ⟨79619866082903771429197421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53079910721935847619464947 79619866082903771429197421)
        ·
          refine ⟨29857449781088914285949033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79619866082903771429197421 29857449781088914285949033)
          ·
            refine ⟨22393087335816685714461775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29857449781088914285949033 22393087335816685714461775)
            ·
              refine ⟨33589631003725028571692663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22393087335816685714461775 33589631003725028571692663)
              ·
                refine ⟨50384446505587542857538995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33589631003725028571692663 50384446505587542857538995)
                ·
                  refine ⟨75576669758381314286308493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50384446505587542857538995 75576669758381314286308493)
                  ·
                    refine ⟨28341251159392992857365685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75576669758381314286308493 28341251159392992857365685)
                    ·
                      refine ⟨2656992296193093080378033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28341251159392992857365685 2656992296193093080378033)
                      ·
                        rfl

theorem cell23_5174474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_5174474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174474 prefixEnd_5174474 := by exact prefixLift 5174474
  have htrace : WordTrace (prefixWord ++ tailWord_5174474) baseStart_5174474 baseEnd_5174474 := by
    simpa [prefixWord, tailWord_5174474, baseEnd_5174474] using wordTrace_append hprefix tailTrace_5174474
  have hstable : (prefixWord ++ tailWord_5174474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174474).length < 2 ^ (prefixWord ++ tailWord_5174474).sum := by decide
  have hdescent : baseEnd_5174474 < baseStart_5174474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174578 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_5174578 : Nat := 118140960795 + 5174578 * 2 ^ 59
def prefixEnd_5174578 : Nat := 4983230072969 + 3 ^ 40 * 5174578 * 2
def baseEnd_5174578 : Nat := 2657045698181160673477555

theorem tailTrace_5174578 : CollatzResearch.WordTrace tailWord_5174578 prefixEnd_5174578 2657045698181160673477555 := by
  unfold tailWord_5174578
  simp only [CollatzResearch.WordTrace]
  refine ⟨47183091161848782102193097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125821576431596752272514925 47183091161848782102193097)
  ·
    refine ⟨35387318371386586576644823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47183091161848782102193097 35387318371386586576644823)
    ·
      refine ⟨53080977557079879864967235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35387318371386586576644823 53080977557079879864967235)
      ·
        refine ⟨79621466335619819797450853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53080977557079879864967235 79621466335619819797450853)
        ·
          refine ⟨14929024937928716212022035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79621466335619819797450853 14929024937928716212022035)
          ·
            refine ⟨22393537406893074318033053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14929024937928716212022035 22393537406893074318033053)
            ·
              refine ⟨8397576527584902869262395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22393537406893074318033053 8397576527584902869262395)
              ·
                refine ⟨12596364791377354303893593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8397576527584902869262395 12596364791377354303893593)
                ·
                  refine ⟨9447273593533015727920195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12596364791377354303893593 9447273593533015727920195)
                  ·
                    refine ⟨14170910390299523591880293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9447273593533015727920195 14170910390299523591880293)
                    ·
                      refine ⟨2657045698181160673477555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14170910390299523591880293 2657045698181160673477555)
                      ·
                        rfl

theorem cell23_5174578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_5174578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174578 prefixEnd_5174578 := by exact prefixLift 5174578
  have htrace : WordTrace (prefixWord ++ tailWord_5174578) baseStart_5174578 baseEnd_5174578 := by
    simpa [prefixWord, tailWord_5174578, baseEnd_5174578] using wordTrace_append hprefix tailTrace_5174578
  have hstable : (prefixWord ++ tailWord_5174578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174578).length < 2 ^ (prefixWord ++ tailWord_5174578).sum := by decide
  have hdescent : baseEnd_5174578 < baseStart_5174578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174584 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 8]
def baseStart_5174584 : Nat := 118140960795 + 5174584 * 2 ^ 59
def prefixEnd_5174584 : Nat := 4983230072969 + 3 ^ 40 * 5174584 * 2
def baseEnd_5174584 : Nat := 295227642118343072222503

theorem tailTrace_5174584 : CollatzResearch.WordTrace tailWord_5174584 prefixEnd_5174584 295227642118343072222503 := by
  unfold tailWord_5174584
  simp only [CollatzResearch.WordTrace]
  refine ⟨94366291742686695716745403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125821722323582260955660537 94366291742686695716745403)
  ·
    refine ⟨141549437614030043575118105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94366291742686695716745403 141549437614030043575118105)
    ·
      refine ⟨106162078210522532681338579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141549437614030043575118105 106162078210522532681338579)
      ·
        refine ⟨159243117315783799022007869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106162078210522532681338579 159243117315783799022007869)
        ·
          refine ⟨59716168993418924633252951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159243117315783799022007869 59716168993418924633252951)
          ·
            refine ⟨89574253490128386949879427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59716168993418924633252951 89574253490128386949879427)
            ·
              refine ⟨134361380235192580424819141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89574253490128386949879427 134361380235192580424819141)
              ·
                refine ⟨25192758794098608829653589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134361380235192580424819141 25192758794098608829653589)
                ·
                  refine ⟨295227642118343072222503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25192758794098608829653589 295227642118343072222503)
                  ·
                    rfl

theorem cell23_5174584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 8].length) (baseStart_5174584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174584 prefixEnd_5174584 := by exact prefixLift 5174584
  have htrace : WordTrace (prefixWord ++ tailWord_5174584) baseStart_5174584 baseEnd_5174584 := by
    simpa [prefixWord, tailWord_5174584, baseEnd_5174584] using wordTrace_append hprefix tailTrace_5174584
  have hstable : (prefixWord ++ tailWord_5174584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174584).length < 2 ^ (prefixWord ++ tailWord_5174584).sum := by decide
  have hdescent : baseEnd_5174584 < baseStart_5174584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174601 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 6]
def baseStart_5174601 : Nat := 118140960795 + 5174601 * 2 ^ 59
def prefixEnd_5174601 : Nat := 4983230072969 + 3 ^ 40 * 5174601 * 2
def baseEnd_5174601 : Nat := 295228612026246009276661

theorem tailTrace_5174601 : CollatzResearch.WordTrace tailWord_5174601 prefixEnd_5174601 295228612026246009276661 := by
  unfold tailWord_5174601
  simp only [CollatzResearch.WordTrace]
  refine ⟨188733203526311803336859657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125822135684207868891239771 188733203526311803336859657)
  ·
    refine ⟨141549902644733852502644743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188733203526311803336859657 141549902644733852502644743)
    ·
      refine ⟨212324853967100778753967115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141549902644733852502644743 212324853967100778753967115)
      ·
        refine ⟨318487280950651168130950673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212324853967100778753967115 318487280950651168130950673)
        ·
          refine ⟨238865460712988376098213005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318487280950651168130950673 238865460712988376098213005)
          ·
            refine ⟨89574547767370641036829877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238865460712988376098213005 89574547767370641036829877)
            ·
              refine ⟨8397613853190997597202801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89574547767370641036829877 8397613853190997597202801)
              ·
                refine ⟨6298210389893248197902101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8397613853190997597202801 6298210389893248197902101)
                ·
                  refine ⟨295228612026246009276661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6298210389893248197902101 295228612026246009276661)
                  ·
                    rfl

theorem cell23_5174601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 6].length) (baseStart_5174601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174601 prefixEnd_5174601 := by exact prefixLift 5174601
  have htrace : WordTrace (prefixWord ++ tailWord_5174601) baseStart_5174601 baseEnd_5174601 := by
    simpa [prefixWord, tailWord_5174601, baseEnd_5174601] using wordTrace_append hprefix tailTrace_5174601
  have hstable : (prefixWord ++ tailWord_5174601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174601).length < 2 ^ (prefixWord ++ tailWord_5174601).sum := by decide
  have hdescent : baseEnd_5174601 < baseStart_5174601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174681 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 6]
def baseStart_5174681 : Nat := 118140960795 + 5174681 * 2 ^ 59
def prefixEnd_5174681 : Nat := 4983230072969 + 3 ^ 40 * 5174681 * 2
def baseEnd_5174681 : Nat := 2657098586688573770489581

theorem tailTrace_5174681 : CollatzResearch.WordTrace tailWord_5174681 prefixEnd_5174681 2657098586688573770489581 := by
  unfold tailWord_5174681
  simp only [CollatzResearch.WordTrace]
  refine ⟨188736121366021976999771897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125824080910681317999847931 188736121366021976999771897)
  ·
    refine ⟨141552091024516482749828923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188736121366021976999771897 141552091024516482749828923)
    ·
      refine ⟨212328136536774724124743385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141552091024516482749828923 212328136536774724124743385)
      ·
        refine ⟨159246102402581043093557539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212328136536774724124743385 159246102402581043093557539)
        ·
          refine ⟨238869153603871564640336309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159246102402581043093557539 238869153603871564640336309)
          ·
            refine ⟨22393983150362959185031529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238869153603871564640336309 22393983150362959185031529)
            ·
              refine ⟨16795487362772219388773647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22393983150362959185031529 16795487362772219388773647)
              ·
                refine ⟨25193231044158329083160471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16795487362772219388773647 25193231044158329083160471)
                ·
                  refine ⟨37789846566237493624740707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25193231044158329083160471 37789846566237493624740707)
                  ·
                    refine ⟨56684769849356240437111061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37789846566237493624740707 56684769849356240437111061)
                    ·
                      refine ⟨2657098586688573770489581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56684769849356240437111061 2657098586688573770489581)
                      ·
                        rfl

theorem cell23_5174681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_5174681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174681 prefixEnd_5174681 := by exact prefixLift 5174681
  have htrace : WordTrace (prefixWord ++ tailWord_5174681) baseStart_5174681 baseEnd_5174681 := by
    simpa [prefixWord, tailWord_5174681, baseEnd_5174681] using wordTrace_append hprefix tailTrace_5174681
  have hstable : (prefixWord ++ tailWord_5174681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174681).length < 2 ^ (prefixWord ++ tailWord_5174681).sum := by decide
  have hdescent : baseEnd_5174681 < baseStart_5174681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174685 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_5174685 : Nat := 118140960795 + 5174685 * 2 ^ 59
def prefixEnd_5174685 : Nat := 4983230072969 + 3 ^ 40 * 5174685 * 2
def baseEnd_5174685 : Nat := 2657100640611191754839563

theorem tailTrace_5174685 : CollatzResearch.WordTrace tailWord_5174685 prefixEnd_5174685 2657100640611191754839563 := by
  unfold tailWord_5174685
  simp only [CollatzResearch.WordTrace]
  refine ⟨188736267258007485682917509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125824178172004990455278339 188736267258007485682917509)
  ·
    refine ⟨35388050110876403565547033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188736267258007485682917509 35388050110876403565547033)
    ·
      refine ⟨26541037583157302674160275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35388050110876403565547033 26541037583157302674160275)
      ·
        refine ⟨39811556374735954011240413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26541037583157302674160275 39811556374735954011240413)
        ·
          refine ⟨14929333640525982754215155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39811556374735954011240413 14929333640525982754215155)
          ·
            refine ⟨22394000460788974131322733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14929333640525982754215155 22394000460788974131322733)
            ·
              refine ⟨8397750172795865299246025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22394000460788974131322733 8397750172795865299246025)
              ·
                refine ⟨6298312629596898974434519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8397750172795865299246025 6298312629596898974434519)
                ·
                  refine ⟨9447468944395348461651779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6298312629596898974434519 9447468944395348461651779)
                  ·
                    refine ⟨14171203416593022692477669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9447468944395348461651779 14171203416593022692477669)
                    ·
                      refine ⟨2657100640611191754839563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14171203416593022692477669 2657100640611191754839563)
                      ·
                        rfl

theorem cell23_5174685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_5174685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174685 prefixEnd_5174685 := by exact prefixLift 5174685
  have htrace : WordTrace (prefixWord ++ tailWord_5174685) baseStart_5174685 baseEnd_5174685 := by
    simpa [prefixWord, tailWord_5174685, baseEnd_5174685] using wordTrace_append hprefix tailTrace_5174685
  have hstable : (prefixWord ++ tailWord_5174685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174685).length < 2 ^ (prefixWord ++ tailWord_5174685).sum := by decide
  have hdescent : baseEnd_5174685 < baseStart_5174685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174688 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 3]
def baseStart_5174688 : Nat := 118140960795 + 5174688 * 2 ^ 59
def prefixEnd_5174688 : Nat := 4983230072969 + 3 ^ 40 * 5174688 * 2
def baseEnd_5174688 : Nat := 2657102181053155243102049

theorem tailTrace_5174688 : CollatzResearch.WordTrace tailWord_5174688 prefixEnd_5174688 2657102181053155243102049 := by
  unfold tailWord_5174688
  simp only [CollatzResearch.WordTrace]
  refine ⟨94368188338498308597638359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125824251117997744796851145 94368188338498308597638359)
  ·
    refine ⟨141552282507747462896457539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94368188338498308597638359 141552282507747462896457539)
    ·
      refine ⟨212328423761621194344686309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141552282507747462896457539 212328423761621194344686309)
      ·
        refine ⟨39811579455303973939628683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212328423761621194344686309 39811579455303973939628683)
        ·
          refine ⟨59717369182955960909443025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39811579455303973939628683 59717369182955960909443025)
          ·
            refine ⟨44788026887216970682082269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59717369182955960909443025 44788026887216970682082269)
            ·
              refine ⟨16795510082706364005780851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44788026887216970682082269 16795510082706364005780851)
              ·
                refine ⟨25193265124059546008671277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16795510082706364005780851 25193265124059546008671277)
                ·
                  refine ⟨9447474421522329753251729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25193265124059546008671277 9447474421522329753251729)
                  ·
                    refine ⟨7085605816141747314938797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9447474421522329753251729 7085605816141747314938797)
                    ·
                      refine ⟨2657102181053155243102049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085605816141747314938797 2657102181053155243102049)
                      ·
                        rfl

theorem cell23_5174688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_5174688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174688 prefixEnd_5174688 := by exact prefixLift 5174688
  have htrace : WordTrace (prefixWord ++ tailWord_5174688) baseStart_5174688 baseEnd_5174688 := by
    simpa [prefixWord, tailWord_5174688, baseEnd_5174688] using wordTrace_append hprefix tailTrace_5174688
  have hstable : (prefixWord ++ tailWord_5174688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174688).length < 2 ^ (prefixWord ++ tailWord_5174688).sum := by decide
  have hdescent : baseEnd_5174688 < baseStart_5174688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174718 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_5174718 : Nat := 118140960795 + 5174718 * 2 ^ 59
def prefixEnd_5174718 : Nat := 4983230072969 + 3 ^ 40 * 5174718 * 2
def baseEnd_5174718 : Nat := 2657117585472790125726911

theorem tailTrace_5174718 : CollatzResearch.WordTrace tailWord_5174718 prefixEnd_5174718 2657117585472790125726911 := by
  unfold tailWord_5174718
  simp only [CollatzResearch.WordTrace]
  refine ⟨23592183858360991539858601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125824980577925288212579205 23592183858360991539858601)
  ·
    refine ⟨17694137893770743654893951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23592183858360991539858601 17694137893770743654893951)
    ·
      refine ⟨26541206840656115482340927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17694137893770743654893951 26541206840656115482340927)
      ·
        refine ⟨39811810260984173223511391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26541206840656115482340927 39811810260984173223511391)
        ·
          refine ⟨59717715391476259835267087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39811810260984173223511391 59717715391476259835267087)
          ·
            refine ⟨89576573087214389752900631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59717715391476259835267087 89576573087214389752900631)
            ·
              refine ⟨134364859630821584629350947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89576573087214389752900631 134364859630821584629350947)
              ·
                refine ⟨201547289446232376944026421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134364859630821584629350947 201547289446232376944026421)
                ·
                  refine ⟨18895058385584285338502477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201547289446232376944026421 18895058385584285338502477)
                  ·
                    refine ⟨7085646894594107001938429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18895058385584285338502477 7085646894594107001938429)
                    ·
                      refine ⟨2657117585472790125726911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085646894594107001938429 2657117585472790125726911)
                      ·
                        rfl

theorem cell23_5174718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_5174718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174718 prefixEnd_5174718 := by exact prefixLift 5174718
  have htrace : WordTrace (prefixWord ++ tailWord_5174718) baseStart_5174718 baseEnd_5174718 := by
    simpa [prefixWord, tailWord_5174718, baseEnd_5174718] using wordTrace_append hprefix tailTrace_5174718
  have hstable : (prefixWord ++ tailWord_5174718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174718).length < 2 ^ (prefixWord ++ tailWord_5174718).sum := by decide
  have hdescent : baseEnd_5174718 < baseStart_5174718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174735 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 3]
def baseStart_5174735 : Nat := 118140960795 + 5174735 * 2 ^ 59
def prefixEnd_5174735 : Nat := 4983230072969 + 3 ^ 40 * 5174735 * 2
def baseEnd_5174735 : Nat := 2657126314643916559214333

theorem tailTrace_5174735 : CollatzResearch.WordTrace tailWord_5174735 prefixEnd_5174735 2657126314643916559214333 := by
  unfold tailWord_5174735
  simp only [CollatzResearch.WordTrace]
  refine ⟨188738090907826344222237659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125825393938550896148158439 188738090907826344222237659)
  ·
    refine ⟨283107136361739516333356489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188738090907826344222237659 283107136361739516333356489)
    ·
      refine ⟨212330352271304637250017367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283107136361739516333356489 212330352271304637250017367)
      ·
        refine ⟨318495528406956955875026051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212330352271304637250017367 318495528406956955875026051)
        ·
          refine ⟨477743292610435433812539077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318495528406956955875026051 477743292610435433812539077)
          ·
            refine ⟨89576867364456643839851077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 477743292610435433812539077 89576867364456643839851077)
            ·
              refine ⟨16795662630835620719972077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89576867364456643839851077 16795662630835620719972077)
              ·
                refine ⟨6298373486563357769989529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16795662630835620719972077 6298373486563357769989529)
                ·
                  refine ⟨4723780114922518327492147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6298373486563357769989529 4723780114922518327492147)
                  ·
                    refine ⟨7085670172383777491238221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4723780114922518327492147 7085670172383777491238221)
                    ·
                      refine ⟨2657126314643916559214333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085670172383777491238221 2657126314643916559214333)
                      ·
                        rfl

theorem cell23_5174735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 3].length) (baseStart_5174735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174735 prefixEnd_5174735 := by exact prefixLift 5174735
  have htrace : WordTrace (prefixWord ++ tailWord_5174735) baseStart_5174735 baseEnd_5174735 := by
    simpa [prefixWord, tailWord_5174735, baseEnd_5174735] using wordTrace_append hprefix tailTrace_5174735
  have hstable : (prefixWord ++ tailWord_5174735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174735).length < 2 ^ (prefixWord ++ tailWord_5174735).sum := by decide
  have hdescent : baseEnd_5174735 < baseStart_5174735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174745 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 3, 3, 2]
def baseStart_5174745 : Nat := 118140960795 + 5174745 * 2 ^ 59
def prefixEnd_5174745 : Nat := 4983230072969 + 3 ^ 40 * 5174745 * 2
def baseEnd_5174745 : Nat := 2657131449450461520089287

theorem tailTrace_5174745 : CollatzResearch.WordTrace tailWord_5174745 prefixEnd_5174745 2657131449450461520089287 := by
  unfold tailWord_5174745
  simp only [CollatzResearch.WordTrace]
  refine ⟨188738455637790115930101689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125825637091860077286734459 188738455637790115930101689)
  ·
    refine ⟨141553841728342586947576267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188738455637790115930101689 141553841728342586947576267)
    ·
      refine ⟨212330762592513880421364401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141553841728342586947576267 212330762592513880421364401)
      ·
        refine ⟨159248071944385410316023301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212330762592513880421364401 159248071944385410316023301)
        ·
          refine ⟨29859013489572264434254369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 159248071944385410316023301 29859013489572264434254369)
          ·
            refine ⟨22394260117179198325690777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29859013489572264434254369 22394260117179198325690777)
            ·
              refine ⟨16795695087884398744268083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22394260117179198325690777 16795695087884398744268083)
              ·
                refine ⟨25193542631826598116402125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16795695087884398744268083 25193542631826598116402125)
                ·
                  refine ⟨9447578486934974293650797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25193542631826598116402125 9447578486934974293650797)
                  ·
                    refine ⟨3542841932600615360119049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9447578486934974293650797 3542841932600615360119049)
                    ·
                      refine ⟨2657131449450461520089287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3542841932600615360119049 2657131449450461520089287)
                      ·
                        rfl

theorem cell23_5174745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_5174745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174745 prefixEnd_5174745 := by exact prefixLift 5174745
  have htrace : WordTrace (prefixWord ++ tailWord_5174745) baseStart_5174745 baseEnd_5174745 := by
    simpa [prefixWord, tailWord_5174745, baseEnd_5174745] using wordTrace_append hprefix tailTrace_5174745
  have hstable : (prefixWord ++ tailWord_5174745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174745).length < 2 ^ (prefixWord ++ tailWord_5174745).sum := by decide
  have hdescent : baseEnd_5174745 < baseStart_5174745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174751 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 1, 8]
def baseStart_5174751 : Nat := 118140960795 + 5174751 * 2 ^ 59
def prefixEnd_5174751 : Nat := 4983230072969 + 3 ^ 40 * 5174751 * 2
def baseEnd_5174751 : Nat := 885711510111462832204753

theorem tailTrace_5174751 : CollatzResearch.WordTrace tailWord_5174751 prefixEnd_5174751 885711510111462832204753 := by
  unfold tailWord_5174751
  simp only [CollatzResearch.WordTrace]
  refine ⟨188738674475768378954820107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125825782983845585969880071 188738674475768378954820107)
  ·
    refine ⟨283108011713652568432230161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188738674475768378954820107 283108011713652568432230161)
    ·
      refine ⟨212331008785239426324172621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283108011713652568432230161 212331008785239426324172621)
      ·
        refine ⟨79624128294464784871564733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212331008785239426324172621 79624128294464784871564733)
        ·
          refine ⟨29859048110424294326836775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79624128294464784871564733 29859048110424294326836775)
          ·
            refine ⟨44788572165636441490255163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29859048110424294326836775 44788572165636441490255163)
            ·
              refine ⟨67182858248454662235382745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44788572165636441490255163 67182858248454662235382745)
              ·
                refine ⟨50387143686340996676537059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67182858248454662235382745 50387143686340996676537059)
                ·
                  refine ⟨75580715529511495014805589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50387143686340996676537059 75580715529511495014805589)
                  ·
                    refine ⟨885711510111462832204753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75580715529511495014805589 885711510111462832204753)
                    ·
                      rfl

theorem cell23_5174751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_5174751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174751 prefixEnd_5174751 := by exact prefixLift 5174751
  have htrace : WordTrace (prefixWord ++ tailWord_5174751) baseStart_5174751 baseEnd_5174751 := by
    simpa [prefixWord, tailWord_5174751, baseEnd_5174751] using wordTrace_append hprefix tailTrace_5174751
  have hstable : (prefixWord ++ tailWord_5174751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174751).length < 2 ^ (prefixWord ++ tailWord_5174751).sum := by decide
  have hdescent : baseEnd_5174751 < baseStart_5174751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174761 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 5]
def baseStart_5174761 : Nat := 118140960795 + 5174761 * 2 ^ 59
def prefixEnd_5174761 : Nat := 4983230072969 + 3 ^ 40 * 5174761 * 2
def baseEnd_5174761 : Nat := 2657139665140933457489213

theorem tailTrace_5174761 : CollatzResearch.WordTrace tailWord_5174761 prefixEnd_5174761 2657139665140933457489213 := by
  unfold tailWord_5174761
  simp only [CollatzResearch.WordTrace]
  refine ⟨188739039205732150662684137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125826026137154767108456091 188739039205732150662684137)
  ·
    refine ⟨141554279404299112997013103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188739039205732150662684137 141554279404299112997013103)
    ·
      refine ⟨212331419106448669495519655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141554279404299112997013103 212331419106448669495519655)
      ·
        refine ⟨318497128659673004243279483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212331419106448669495519655 318497128659673004243279483)
        ·
          refine ⟨477745692989509506364919225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318497128659673004243279483 477745692989509506364919225)
          ·
            refine ⟨358309269742132129773689419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477745692989509506364919225 358309269742132129773689419)
            ·
              refine ⟨537463904613198194660534129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358309269742132129773689419 537463904613198194660534129)
              ·
                refine ⟨403097928459898645995400597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537463904613198194660534129 403097928459898645995400597)
                ·
                  refine ⟨18895215396557749031034403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 403097928459898645995400597 18895215396557749031034403)
                  ·
                    refine ⟨28342823094836623546551605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18895215396557749031034403 28342823094836623546551605)
                    ·
                      refine ⟨2657139665140933457489213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28342823094836623546551605 2657139665140933457489213)
                      ·
                        rfl

theorem cell23_5174761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_5174761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174761 prefixEnd_5174761 := by exact prefixLift 5174761
  have htrace : WordTrace (prefixWord ++ tailWord_5174761) baseStart_5174761 baseEnd_5174761 := by
    simpa [prefixWord, tailWord_5174761, baseEnd_5174761] using wordTrace_append hprefix tailTrace_5174761
  have hstable : (prefixWord ++ tailWord_5174761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174761).length < 2 ^ (prefixWord ++ tailWord_5174761).sum := by decide
  have hdescent : baseEnd_5174761 < baseStart_5174761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174786 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5174786 : Nat := 118140960795 + 5174786 * 2 ^ 59
def prefixEnd_5174786 : Nat := 4983230072969 + 3 ^ 40 * 5174786 * 2
def baseEnd_5174786 : Nat := 2657152502157295859676599

theorem tailTrace_5174786 : CollatzResearch.WordTrace tailWord_5174786 prefixEnd_5174786 2657152502157295859676599 := by
  unfold tailWord_5174786
  simp only [CollatzResearch.WordTrace]
  refine ⟨47184987757660394983086053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125826634020427719954896141 47184987757660394983086053)
  ·
    refine ⟨8847185204561324059328635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47184987757660394983086053 8847185204561324059328635)
    ·
      refine ⟨13270777806841986088992953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8847185204561324059328635 13270777806841986088992953)
      ·
        refine ⟨9953083355131489566744715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13270777806841986088992953 9953083355131489566744715)
        ·
          refine ⟨14929625032697234350117073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9953083355131489566744715 14929625032697234350117073)
          ·
            refine ⟨11197218774522925762587805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14929625032697234350117073 11197218774522925762587805)
            ·
              refine ⟨4198957040446097160970427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11197218774522925762587805 4198957040446097160970427)
              ·
                refine ⟨6298435560669145741455641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4198957040446097160970427 6298435560669145741455641)
                ·
                  refine ⟨4723826670501859306091731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6298435560669145741455641 4723826670501859306091731)
                  ·
                    refine ⟨7085740005752788959137597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4723826670501859306091731 7085740005752788959137597)
                    ·
                      refine ⟨2657152502157295859676599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085740005752788959137597 2657152502157295859676599)
                      ·
                        rfl

theorem cell23_5174786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5174786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174786 prefixEnd_5174786 := by exact prefixLift 5174786
  have htrace : WordTrace (prefixWord ++ tailWord_5174786) baseStart_5174786 baseEnd_5174786 := by
    simpa [prefixWord, tailWord_5174786, baseEnd_5174786] using wordTrace_append hprefix tailTrace_5174786
  have hstable : (prefixWord ++ tailWord_5174786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174786).length < 2 ^ (prefixWord ++ tailWord_5174786).sum := by decide
  have hdescent : baseEnd_5174786 < baseStart_5174786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174792 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_5174792 : Nat := 118140960795 + 5174792 * 2 ^ 59
def prefixEnd_5174792 : Nat := 4983230072969 + 3 ^ 40 * 5174792 * 2
def baseEnd_5174792 : Nat := 2657155583041222836201571

theorem tailTrace_5174792 : CollatzResearch.WordTrace tailWord_5174792 prefixEnd_5174792 2657155583041222836201571 := by
  unfold tailWord_5174792
  simp only [CollatzResearch.WordTrace]
  refine ⟨94370084934309921478531315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125826779912413228638041753 94370084934309921478531315)
  ·
    refine ⟨141555127401464882217796973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94370084934309921478531315 141555127401464882217796973)
    ·
      refine ⟨53083172775549330831673865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141555127401464882217796973 53083172775549330831673865)
      ·
        refine ⟨39812379581661998123755399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53083172775549330831673865 39812379581661998123755399)
        ·
          refine ⟨59718569372492997185633099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39812379581661998123755399 59718569372492997185633099)
          ·
            refine ⟨89577854058739495778449649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59718569372492997185633099 89577854058739495778449649)
            ·
              refine ⟨67183390544054621833837237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89577854058739495778449649 67183390544054621833837237)
              ·
                refine ⟨6298442863505120796922241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67183390544054621833837237 6298442863505120796922241)
                ·
                  refine ⟨4723832147628840597691681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6298442863505120796922241 4723832147628840597691681)
                  ·
                    refine ⟨3542874110721630448268761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4723832147628840597691681 3542874110721630448268761)
                    ·
                      refine ⟨2657155583041222836201571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3542874110721630448268761 2657155583041222836201571)
                      ·
                        rfl

theorem cell23_5174792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_5174792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174792 prefixEnd_5174792 := by exact prefixLift 5174792
  have htrace : WordTrace (prefixWord ++ tailWord_5174792) baseStart_5174792 baseEnd_5174792 := by
    simpa [prefixWord, tailWord_5174792, baseEnd_5174792] using wordTrace_append hprefix tailTrace_5174792
  have hstable : (prefixWord ++ tailWord_5174792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174792).length < 2 ^ (prefixWord ++ tailWord_5174792).sum := by decide
  have hdescent : baseEnd_5174792 < baseStart_5174792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174815 : List Nat := [1, 1, 2, 4, 1, 1, 5, 3, 5]
def baseStart_5174815 : Nat := 118140960795 + 5174815 * 2 ^ 59
def prefixEnd_5174815 : Nat := 4983230072969 + 3 ^ 40 * 5174815 * 2
def baseEnd_5174815 : Nat := 295240821455141805134885

theorem tailTrace_5174815 : CollatzResearch.WordTrace tailWord_5174815 prefixEnd_5174815 295240821455141805134885 := by
  unfold tailWord_5174815
  simp only [CollatzResearch.WordTrace]
  refine ⟨188741008747536517885149899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125827339165024345256766599 188741008747536517885149899)
  ·
    refine ⟨283111513121304776827724849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188741008747536517885149899 283111513121304776827724849)
    ·
      refine ⟨212333634840978582620793637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283111513121304776827724849 212333634840978582620793637)
      ·
        refine ⟨39812556532683484241398807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212333634840978582620793637 39812556532683484241398807)
        ·
          refine ⟨59718834799025226362098211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39812556532683484241398807 59718834799025226362098211)
          ·
            refine ⟨89578252198537839543147317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59718834799025226362098211 89578252198537839543147317)
            ·
              refine ⟨8397961143612922457170061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89578252198537839543147317 8397961143612922457170061)
              ·
                refine ⟨3149235428854845921438773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8397961143612922457170061 3149235428854845921438773)
                ·
                  refine ⟨295240821455141805134885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3149235428854845921438773 295240821455141805134885)
                  ·
                    rfl

theorem cell23_5174815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 5].length) (baseStart_5174815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174815 prefixEnd_5174815 := by exact prefixLift 5174815
  have htrace : WordTrace (prefixWord ++ tailWord_5174815) baseStart_5174815 baseEnd_5174815 := by
    simpa [prefixWord, tailWord_5174815, baseEnd_5174815] using wordTrace_append hprefix tailTrace_5174815
  have hstable : (prefixWord ++ tailWord_5174815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174815).length < 2 ^ (prefixWord ++ tailWord_5174815).sum := by decide
  have hdescent : baseEnd_5174815 < baseStart_5174815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174831 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_5174831 : Nat := 118140960795 + 5174831 * 2 ^ 59
def prefixEnd_5174831 : Nat := 4983230072969 + 3 ^ 40 * 5174831 * 2
def baseEnd_5174831 : Nat := 2657175608786748183613891

theorem tailTrace_5174831 : CollatzResearch.WordTrace tailWord_5174831 prefixEnd_5174831 2657175608786748183613891 := by
  unfold tailWord_5174831
  simp only [CollatzResearch.WordTrace]
  refine ⟨188741592315478552617732347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125827728210319035078488231 188741592315478552617732347)
  ·
    refine ⟨283112388473217828926598521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188741592315478552617732347 283112388473217828926598521)
    ·
      refine ⟨212334291354913371694948891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283112388473217828926598521 212334291354913371694948891)
      ·
        refine ⟨318501437032370057542423337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212334291354913371694948891 318501437032370057542423337)
        ·
          refine ⟨238876077774277543156817503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318501437032370057542423337 238876077774277543156817503)
          ·
            refine ⟨358314116661416314735226255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238876077774277543156817503 358314116661416314735226255)
            ·
              refine ⟨537471174992124472102839383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358314116661416314735226255 537471174992124472102839383)
              ·
                refine ⟨806206762488186708154259075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537471174992124472102839383 806206762488186708154259075)
                ·
                  refine ⟨1209310143732280062231388613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806206762488186708154259075 1209310143732280062231388613)
                  ·
                    refine ⟨226745651949802511668385365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1209310143732280062231388613 226745651949802511668385365)
                    ·
                      refine ⟨2657175608786748183613891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 226745651949802511668385365 2657175608786748183613891)
                      ·
                        rfl

theorem cell23_5174831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_5174831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174831 prefixEnd_5174831 := by exact prefixLift 5174831
  have htrace : WordTrace (prefixWord ++ tailWord_5174831) baseStart_5174831 baseEnd_5174831 := by
    simpa [prefixWord, tailWord_5174831, baseEnd_5174831] using wordTrace_append hprefix tailTrace_5174831
  have hstable : (prefixWord ++ tailWord_5174831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174831).length < 2 ^ (prefixWord ++ tailWord_5174831).sum := by decide
  have hdescent : baseEnd_5174831 < baseStart_5174831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174848 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 4]
def baseStart_5174848 : Nat := 118140960795 + 5174848 * 2 ^ 59
def prefixEnd_5174848 : Nat := 4983230072969 + 3 ^ 40 * 5174848 * 2
def baseEnd_5174848 : Nat := 2657184337957874617101313

theorem tailTrace_5174848 : CollatzResearch.WordTrace tailWord_5174848 prefixEnd_5174848 2657184337957874617101313 := by
  unfold tailWord_5174848
  simp only [CollatzResearch.WordTrace]
  refine ⟨94371106178208482260550599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125828141570944643014067465 94371106178208482260550599)
  ·
    refine ⟨141556659267312723390825899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94371106178208482260550599 141556659267312723390825899)
    ·
      refine ⟨212334988900969085086238849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141556659267312723390825899 212334988900969085086238849)
      ·
        refine ⟨159251241675726813814679137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212334988900969085086238849 159251241675726813814679137)
        ·
          refine ⟨119438431256795110361009353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159251241675726813814679137 119438431256795110361009353)
          ·
            refine ⟨89578823442596332770757015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119438431256795110361009353 89578823442596332770757015)
            ·
              refine ⟨134368235163894499156135523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89578823442596332770757015 134368235163894499156135523)
              ·
                refine ⟨201552352745841748734203285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134368235163894499156135523 201552352745841748734203285)
                ·
                  refine ⟨9447766534961331971915779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 201552352745841748734203285 9447766534961331971915779)
                  ·
                    refine ⟨14171649802441997957873669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9447766534961331971915779 14171649802441997957873669)
                    ·
                      refine ⟨2657184337957874617101313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14171649802441997957873669 2657184337957874617101313)
                      ·
                        rfl

theorem cell23_5174848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_5174848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174848 prefixEnd_5174848 := by exact prefixLift 5174848
  have htrace : WordTrace (prefixWord ++ tailWord_5174848) baseStart_5174848 baseEnd_5174848 := by
    simpa [prefixWord, tailWord_5174848, baseEnd_5174848] using wordTrace_append hprefix tailTrace_5174848
  have hstable : (prefixWord ++ tailWord_5174848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174848).length < 2 ^ (prefixWord ++ tailWord_5174848).sum := by decide
  have hdescent : baseEnd_5174848 < baseStart_5174848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174865 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 4]
def baseStart_5174865 : Nat := 118140960795 + 5174865 * 2 ^ 59
def prefixEnd_5174865 : Nat := 4983230072969 + 3 ^ 40 * 5174865 * 2
def baseEnd_5174865 : Nat := 2657193067129001050588735

theorem tailTrace_5174865 : CollatzResearch.WordTrace tailWord_5174865 prefixEnd_5174865 2657193067129001050588735 := by
  unfold tailWord_5174865
  simp only [CollatzResearch.WordTrace]
  refine ⟨188742832397355376424470049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125828554931570250949646699 188742832397355376424470049)
  ·
    refine ⟨141557124298016532318352537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188742832397355376424470049 141557124298016532318352537)
    ·
      refine ⟨106167843223512399238764403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141557124298016532318352537 106167843223512399238764403)
      ·
        refine ⟨159251764835268598858146605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106167843223512399238764403 159251764835268598858146605)
        ·
          refine ⟨59719411813225724571804977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159251764835268598858146605 59719411813225724571804977)
          ·
            refine ⟨44789558859919293428853733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59719411813225724571804977 44789558859919293428853733)
            ·
              refine ⟨8398042286234867517910075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44789558859919293428853733 8398042286234867517910075)
              ·
                refine ⟨12597063429352301276865113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8398042286234867517910075 12597063429352301276865113)
                ·
                  refine ⟨9447797572014225957648835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12597063429352301276865113 9447797572014225957648835)
                  ·
                    refine ⟨14171696358021338936473253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9447797572014225957648835 14171696358021338936473253)
                    ·
                      refine ⟨2657193067129001050588735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14171696358021338936473253 2657193067129001050588735)
                      ·
                        rfl

theorem cell23_5174865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 4].length) (baseStart_5174865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174865 prefixEnd_5174865 := by exact prefixLift 5174865
  have htrace : WordTrace (prefixWord ++ tailWord_5174865) baseStart_5174865 baseEnd_5174865 := by
    simpa [prefixWord, tailWord_5174865, baseEnd_5174865] using wordTrace_append hprefix tailTrace_5174865
  have hstable : (prefixWord ++ tailWord_5174865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174865).length < 2 ^ (prefixWord ++ tailWord_5174865).sum := by decide
  have hdescent : baseEnd_5174865 < baseStart_5174865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174949 : List Nat := [1, 3, 1, 2, 1, 2, 4, 4, 1, 1, 3]
def baseStart_5174949 : Nat := 118140960795 + 5174949 * 2 ^ 59
def prefixEnd_5174949 : Nat := 4983230072969 + 3 ^ 40 * 5174949 * 2
def baseEnd_5174949 : Nat := 2657236199503978721938349

theorem tailTrace_5174949 : CollatzResearch.WordTrace tailWord_5174949 prefixEnd_5174949 2657236199503978721938349 := by
  unfold tailWord_5174949
  simp only [CollatzResearch.WordTrace]
  refine ⟨188745896129051058770527901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125830597419367372513685267 188745896129051058770527901)
  ·
    refine ⟨70779711048394147038947963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188745896129051058770527901 70779711048394147038947963)
    ·
      refine ⟨106169566572591220558421945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70779711048394147038947963 106169566572591220558421945)
      ·
        refine ⟨79627174929443415418816459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106169566572591220558421945 79627174929443415418816459)
        ·
          refine ⟨119440762394165123128224689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79627174929443415418816459 119440762394165123128224689)
          ·
            refine ⟨89580571795623842346168517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119440762394165123128224689 89580571795623842346168517)
            ·
              refine ⟨16796357211679470439906597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89580571795623842346168517 16796357211679470439906597)
              ·
                refine ⟨3149316977189900707482487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16796357211679470439906597 3149316977189900707482487)
                ·
                  refine ⟨4723975465784851061223731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149316977189900707482487 4723975465784851061223731)
                  ·
                    refine ⟨7085963198677276591835597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4723975465784851061223731 7085963198677276591835597)
                    ·
                      refine ⟨2657236199503978721938349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085963198677276591835597 2657236199503978721938349)
                      ·
                        rfl

theorem cell23_5174949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_5174949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174949 prefixEnd_5174949 := by exact prefixLift 5174949
  have htrace : WordTrace (prefixWord ++ tailWord_5174949) baseStart_5174949 baseEnd_5174949 := by
    simpa [prefixWord, tailWord_5174949, baseEnd_5174949] using wordTrace_append hprefix tailTrace_5174949
  have hstable : (prefixWord ++ tailWord_5174949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174949).length < 2 ^ (prefixWord ++ tailWord_5174949).sum := by decide
  have hdescent : baseEnd_5174949 < baseStart_5174949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174966 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_5174966 : Nat := 118140960795 + 5174966 * 2 ^ 59
def prefixEnd_5174966 : Nat := 4983230072969 + 3 ^ 40 * 5174966 * 2
def baseEnd_5174966 : Nat := 2657244928675105155425771

theorem tailTrace_5174966 : CollatzResearch.WordTrace tailWord_5174966 prefixEnd_5174966 2657244928675105155425771 := by
  unfold tailWord_5174966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11796657260624341917118547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125831010779992980449264501 11796657260624341917118547)
  ·
    refine ⟨17694985890936512875677821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11796657260624341917118547 17694985890936512875677821)
    ·
      refine ⟨6635619709101192328379183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17694985890936512875677821 6635619709101192328379183)
      ·
        refine ⟨9953429563651788492568775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6635619709101192328379183 9953429563651788492568775)
        ·
          refine ⟨14930144345477682738853163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9953429563651788492568775 14930144345477682738853163)
          ·
            refine ⟨22395216518216524108279745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14930144345477682738853163 22395216518216524108279745)
            ·
              refine ⟨16796412388662393081209809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22395216518216524108279745 16796412388662393081209809)
              ·
                refine ⟨12597309291496794810907357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16796412388662393081209809 12597309291496794810907357)
                ·
                  refine ⟨4723990984311298054090259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12597309291496794810907357 4723990984311298054090259)
                  ·
                    refine ⟨7085986476466947081135389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4723990984311298054090259 7085986476466947081135389)
                    ·
                      refine ⟨2657244928675105155425771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7085986476466947081135389 2657244928675105155425771)
                      ·
                        rfl

theorem cell23_5174966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_5174966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174966 prefixEnd_5174966 := by exact prefixLift 5174966
  have htrace : WordTrace (prefixWord ++ tailWord_5174966) baseStart_5174966 baseEnd_5174966 := by
    simpa [prefixWord, tailWord_5174966, baseEnd_5174966] using wordTrace_append hprefix tailTrace_5174966
  have hstable : (prefixWord ++ tailWord_5174966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174966).length < 2 ^ (prefixWord ++ tailWord_5174966).sum := by decide
  have hdescent : baseEnd_5174966 < baseStart_5174966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5174972 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_5174972 : Nat := 118140960795 + 5174972 * 2 ^ 59
def prefixEnd_5174972 : Nat := 4983230072969 + 3 ^ 40 * 5174972 * 2
def baseEnd_5174972 : Nat := 2657248009559032131950743

theorem tailTrace_5174972 : CollatzResearch.WordTrace tailWord_5174972 prefixEnd_5174972 2657248009559032131950743 := by
  unfold tailWord_5174972
  simp only [CollatzResearch.WordTrace]
  refine ⟨94373367503983866849307585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125831156671978489132410113 94373367503983866849307585)
  ·
    refine ⟨70780025627987900136980689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94373367503983866849307585 70780025627987900136980689)
    ·
      refine ⟨53085019220990925102735517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70780025627987900136980689 53085019220990925102735517)
      ·
        refine ⟨19906882207871596913525819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53085019220990925102735517 19906882207871596913525819)
        ·
          refine ⟨29860323311807395370288729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19906882207871596913525819 29860323311807395370288729)
          ·
            refine ⟨22395242483855546527716547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29860323311807395370288729 22395242483855546527716547)
            ·
              refine ⟨33592863725783319791574821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22395242483855546527716547 33592863725783319791574821)
              ·
                refine ⟨6298661948584372460920279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33592863725783319791574821 6298661948584372460920279)
                ·
                  refine ⟨9447992922876558691380419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6298661948584372460920279 9447992922876558691380419)
                  ·
                    refine ⟨14171989384314838037070629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9447992922876558691380419 14171989384314838037070629)
                    ·
                      refine ⟨2657248009559032131950743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14171989384314838037070629 2657248009559032131950743)
                      ·
                        rfl

theorem cell23_5174972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_5174972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5174972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5174972 prefixEnd_5174972 := by exact prefixLift 5174972
  have htrace : WordTrace (prefixWord ++ tailWord_5174972) baseStart_5174972 baseEnd_5174972 := by
    simpa [prefixWord, tailWord_5174972, baseEnd_5174972] using wordTrace_append hprefix tailTrace_5174972
  have hstable : (prefixWord ++ tailWord_5174972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5174972).length < 2 ^ (prefixWord ++ tailWord_5174972).sum := by decide
  have hdescent : baseEnd_5174972 < baseStart_5174972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5174972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175016 : List Nat := [2, 1, 4, 1, 3, 3, 2, 1, 2, 4]
def baseStart_5175016 : Nat := 118140960795 + 5175016 * 2 ^ 59
def prefixEnd_5175016 : Nat := 4983230072969 + 3 ^ 40 * 5175016 * 2
def baseEnd_5175016 : Nat := 885756867569276653266847

theorem tailTrace_5175016 : CollatzResearch.WordTrace tailWord_5175016 prefixEnd_5175016 885756867569276653266847 := by
  unfold tailWord_5175016
  simp only [CollatzResearch.WordTrace]
  refine ⟨94374169909904164606608451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125832226546538886142144601 94374169909904164606608451)
  ·
    refine ⟨141561254864856246909912677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94374169909904164606608451 141561254864856246909912677)
    ·
      refine ⟨26542735287160546295608627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141561254864856246909912677 26542735287160546295608627)
      ·
        refine ⟨39814102930740819443412941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26542735287160546295608627 39814102930740819443412941)
        ·
          refine ⟨14930288599027807291279853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39814102930740819443412941 14930288599027807291279853)
          ·
            refine ⟨5598858224635427734229945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14930288599027807291279853 5598858224635427734229945)
            ·
              refine ⟨4199143668476570800672459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5598858224635427734229945 4199143668476570800672459)
              ·
                refine ⟨6298715502714856201008689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4199143668476570800672459 6298715502714856201008689)
                ·
                  refine ⟨4724036627036142150756517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6298715502714856201008689 4724036627036142150756517)
                  ·
                    refine ⟨885756867569276653266847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724036627036142150756517 885756867569276653266847)
                    ·
                      rfl

theorem cell23_5175016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_5175016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175016 prefixEnd_5175016 := by exact prefixLift 5175016
  have htrace : WordTrace (prefixWord ++ tailWord_5175016) baseStart_5175016 baseEnd_5175016 := by
    simpa [prefixWord, tailWord_5175016, baseEnd_5175016] using wordTrace_append hprefix tailTrace_5175016
  have hstable : (prefixWord ++ tailWord_5175016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175016).length < 2 ^ (prefixWord ++ tailWord_5175016).sum := by decide
  have hdescent : baseEnd_5175016 < baseStart_5175016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175022 : List Nat := [4, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_5175022 : Nat := 118140960795 + 5175022 * 2 ^ 59
def prefixEnd_5175022 : Nat := 4983230072969 + 3 ^ 40 * 5175022 * 2
def baseEnd_5175022 : Nat := 2657273683591756936325513

theorem tailTrace_5175022 : CollatzResearch.WordTrace tailWord_5175022 prefixEnd_5175022 2657273683591756936325513 := by
  unfold tailWord_5175022
  simp only [CollatzResearch.WordTrace]
  refine ⟨23593569832223324029741915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125832372438524394825290213 23593569832223324029741915)
  ·
    refine ⟨35390354748334986044612873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23593569832223324029741915 35390354748334986044612873)
    ·
      refine ⟨26542766061251239533459655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35390354748334986044612873 26542766061251239533459655)
      ·
        refine ⟨39814149091876859300189483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26542766061251239533459655 39814149091876859300189483)
        ·
          refine ⟨59721223637815288950284225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39814149091876859300189483 59721223637815288950284225)
          ·
            refine ⟨44790917728361466712713169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59721223637815288950284225 44790917728361466712713169)
            ·
              refine ⟨33593188296271100034534877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44790917728361466712713169 33593188296271100034534877)
              ·
                refine ⟨12597445611101662512950579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33593188296271100034534877 12597445611101662512950579)
                ·
                  refine ⟨18896168416652493769425869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12597445611101662512950579 18896168416652493769425869)
                  ·
                    refine ⟨7086063156244685163534701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18896168416652493769425869 7086063156244685163534701)
                    ·
                      refine ⟨2657273683591756936325513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7086063156244685163534701 2657273683591756936325513)
                      ·
                        rfl

theorem cell23_5175022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_5175022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175022 prefixEnd_5175022 := by exact prefixLift 5175022
  have htrace : WordTrace (prefixWord ++ tailWord_5175022) baseStart_5175022 baseEnd_5175022 := by
    simpa [prefixWord, tailWord_5175022, baseEnd_5175022] using wordTrace_append hprefix tailTrace_5175022
  have hstable : (prefixWord ++ tailWord_5175022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175022).length < 2 ^ (prefixWord ++ tailWord_5175022).sum := by decide
  have hdescent : baseEnd_5175022 < baseStart_5175022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175046 : List Nat := [6, 2, 2, 1, 12]
def baseStart_5175046 : Nat := 118140960795 + 5175046 * 2 ^ 59
def prefixEnd_5175046 : Nat := 4983230072969 + 3 ^ 40 * 5175046 * 2
def baseEnd_5175046 : Nat := 3645111120888154790707

theorem tailTrace_5175046 : CollatzResearch.WordTrace tailWord_5175046 prefixEnd_5175046 3645111120888154790707 := by
  unfold tailWord_5175046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5898419812803113885525281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125832956006466429557872661 5898419812803113885525281)
  ·
    refine ⟨4423814859602335414143961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5898419812803113885525281 4423814859602335414143961)
    ·
      refine ⟨3317861144701751560607971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4423814859602335414143961 3317861144701751560607971)
      ·
        refine ⟨4976791717052627340911957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3317861144701751560607971 4976791717052627340911957)
        ·
          refine ⟨3645111120888154790707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4976791717052627340911957 3645111120888154790707)
          ·
            rfl

theorem cell23_5175046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 12].length) (baseStart_5175046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175046 prefixEnd_5175046 := by exact prefixLift 5175046
  have htrace : WordTrace (prefixWord ++ tailWord_5175046) baseStart_5175046 baseEnd_5175046 := by
    simpa [prefixWord, tailWord_5175046, baseEnd_5175046] using wordTrace_append hprefix tailTrace_5175046
  have hstable : (prefixWord ++ tailWord_5175046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175046).length < 2 ^ (prefixWord ++ tailWord_5175046).sum := by decide
  have hdescent : baseEnd_5175046 < baseStart_5175046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175075 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 4]
def baseStart_5175075 : Nat := 118140960795 + 5175075 * 2 ^ 59
def prefixEnd_5175075 : Nat := 4983230072969 + 3 ^ 40 * 5175075 * 2
def baseEnd_5175075 : Nat := 2657300898066445228962769

theorem tailTrace_5175075 : CollatzResearch.WordTrace tailWord_5175075 prefixEnd_5175075 2657300898066445228962769 := by
  unfold tailWord_5175075
  simp only [CollatzResearch.WordTrace]
  refine ⟨188750491726594582289614679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125833661151063054859743119 188750491726594582289614679)
  ·
    refine ⟨283125737589891873434422019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188750491726594582289614679 283125737589891873434422019)
    ·
      refine ⟨424688606384837810151633029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283125737589891873434422019 424688606384837810151633029)
      ·
        refine ⟨79629113697157089403431193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 424688606384837810151633029 79629113697157089403431193)
        ·
          refine ⟨59721835272867817052573395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79629113697157089403431193 59721835272867817052573395)
          ·
            refine ⟨89582752909301725578860093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59721835272867817052573395 89582752909301725578860093)
            ·
              refine ⟨33593532340988147092072535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89582752909301725578860093 33593532340988147092072535)
              ·
                refine ⟨50390298511482220638108803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33593532340988147092072535 50390298511482220638108803)
                ·
                  refine ⟨75585447767223330957163205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50390298511482220638108803 75585447767223330957163205)
                  ·
                    refine ⟨14172271456354374554468101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75585447767223330957163205 14172271456354374554468101)
                    ·
                      refine ⟨2657300898066445228962769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14172271456354374554468101 2657300898066445228962769)
                      ·
                        rfl

theorem cell23_5175075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_5175075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175075 prefixEnd_5175075 := by exact prefixLift 5175075
  have htrace : WordTrace (prefixWord ++ tailWord_5175075) baseStart_5175075 baseEnd_5175075 := by
    simpa [prefixWord, tailWord_5175075, baseEnd_5175075] using wordTrace_append hprefix tailTrace_5175075
  have hstable : (prefixWord ++ tailWord_5175075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175075).length < 2 ^ (prefixWord ++ tailWord_5175075).sum := by decide
  have hdescent : baseEnd_5175075 < baseStart_5175075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175112 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_5175112 : Nat := 118140960795 + 5175112 * 2 ^ 59
def prefixEnd_5175112 : Nat := 4983230072969 + 3 ^ 40 * 5175112 * 2
def baseEnd_5175112 : Nat := 2657319896850661584200099

theorem tailTrace_5175112 : CollatzResearch.WordTrace tailWord_5175112 prefixEnd_5175112 2657319896850661584200099 := by
  unfold tailWord_5175112
  simp only [CollatzResearch.WordTrace]
  refine ⟨94375920613730268804355795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125834560818307025072474393 94375920613730268804355795)
  ·
    refine ⟨141563880920595403206533693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94375920613730268804355795 141563880920595403206533693)
    ·
      refine ⟨53086455345223276202450135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141563880920595403206533693 53086455345223276202450135)
      ·
        refine ⟨79629683017834914303675203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53086455345223276202450135 79629683017834914303675203)
        ·
          refine ⟨119444524526752371455512805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79629683017834914303675203 119444524526752371455512805)
          ·
            refine ⟨22395848348766069647908651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119444524526752371455512805 22395848348766069647908651)
            ·
              refine ⟨33593772523149104471862977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22395848348766069647908651 33593772523149104471862977)
              ·
                refine ⟨25195329392361828353897233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33593772523149104471862977 25195329392361828353897233)
                ·
                  refine ⟨18896497044271371265422925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25195329392361828353897233 18896497044271371265422925)
                  ·
                    refine ⟨7086186391601764224533597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18896497044271371265422925 7086186391601764224533597)
                    ·
                      refine ⟨2657319896850661584200099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7086186391601764224533597 2657319896850661584200099)
                      ·
                        rfl

theorem cell23_5175112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_5175112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175112 prefixEnd_5175112 := by exact prefixLift 5175112
  have htrace : WordTrace (prefixWord ++ tailWord_5175112) baseStart_5175112 baseEnd_5175112 := by
    simpa [prefixWord, tailWord_5175112, baseEnd_5175112] using wordTrace_append hprefix tailTrace_5175112
  have hstable : (prefixWord ++ tailWord_5175112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175112).length < 2 ^ (prefixWord ++ tailWord_5175112).sum := by decide
  have hdescent : baseEnd_5175112 < baseStart_5175112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175152 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 4]
def baseStart_5175152 : Nat := 118140960795 + 5175152 * 2 ^ 59
def prefixEnd_5175152 : Nat := 4983230072969 + 3 ^ 40 * 5175152 * 2
def baseEnd_5175152 : Nat := 2657340436076841427699915

theorem tailTrace_5175152 : CollatzResearch.WordTrace tailWord_5175152 prefixEnd_5175152 2657340436076841427699915 := by
  unfold tailWord_5175152
  simp only [CollatzResearch.WordTrace]
  refine ⟨94376650073657812220083855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125835533431543749626778473 94376650073657812220083855)
  ·
    refine ⟨141564975110486718330125783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94376650073657812220083855 141564975110486718330125783)
    ·
      refine ⟨212347462665730077495188675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141564975110486718330125783 212347462665730077495188675)
      ·
        refine ⟨318521193998595116242783013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212347462665730077495188675 318521193998595116242783013)
        ·
          refine ⟨59722723874736584295521815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318521193998595116242783013 59722723874736584295521815)
          ·
            refine ⟨89584085812104876443282723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59722723874736584295521815 89584085812104876443282723)
            ·
              refine ⟨134376128718157314664924085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89584085812104876443282723 134376128718157314664924085)
              ·
                refine ⟨12597762067327248249836633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134376128718157314664924085 12597762067327248249836633)
                ·
                  refine ⟨9448321550495436187377475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12597762067327248249836633 9448321550495436187377475)
                  ·
                    refine ⟨14172482325743154281066213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9448321550495436187377475 14172482325743154281066213)
                    ·
                      refine ⟨2657340436076841427699915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14172482325743154281066213 2657340436076841427699915)
                      ·
                        rfl

theorem cell23_5175152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_5175152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175152 prefixEnd_5175152 := by exact prefixLift 5175152
  have htrace : WordTrace (prefixWord ++ tailWord_5175152) baseStart_5175152 baseEnd_5175152 := by
    simpa [prefixWord, tailWord_5175152, baseEnd_5175152] using wordTrace_append hprefix tailTrace_5175152
  have hstable : (prefixWord ++ tailWord_5175152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175152).length < 2 ^ (prefixWord ++ tailWord_5175152).sum := by decide
  have hdescent : baseEnd_5175152 < baseStart_5175152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175155 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 5]
def baseStart_5175155 : Nat := 118140960795 + 5175155 * 2 ^ 59
def prefixEnd_5175155 : Nat := 4983230072969 + 3 ^ 40 * 5175155 * 2
def baseEnd_5175155 : Nat := 2657341976518804915962401

theorem tailTrace_5175155 : CollatzResearch.WordTrace tailWord_5175155 prefixEnd_5175155 2657341976518804915962401 := by
  unfold tailWord_5175155
  simp only [CollatzResearch.WordTrace]
  refine ⟨188753409566304755952526919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125835606377536503968351279 188753409566304755952526919)
  ·
    refine ⟨283130114349457133928790379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188753409566304755952526919 283130114349457133928790379)
    ·
      refine ⟨424695171524185700893185569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283130114349457133928790379 424695171524185700893185569)
      ·
        refine ⟨318521378643139275669889177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424695171524185700893185569 318521378643139275669889177)
        ·
          refine ⟨238891033982354456752416883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318521378643139275669889177 238891033982354456752416883)
          ·
            refine ⟨358336550973531685128625325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238891033982354456752416883 358336550973531685128625325)
            ·
              refine ⟨134376206615074381923234497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358336550973531685128625325 134376206615074381923234497)
              ·
                refine ⟨100782154961305786442425873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134376206615074381923234497 100782154961305786442425873)
                ·
                  refine ⟨75586616220979339831819405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100782154961305786442425873 75586616220979339831819405)
                  ·
                    refine ⟨28344981082867252436932277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75586616220979339831819405 28344981082867252436932277)
                    ·
                      refine ⟨2657341976518804915962401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28344981082867252436932277 2657341976518804915962401)
                      ·
                        rfl

theorem cell23_5175155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_5175155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175155 prefixEnd_5175155 := by exact prefixLift 5175155
  have htrace : WordTrace (prefixWord ++ tailWord_5175155) baseStart_5175155 baseEnd_5175155 := by
    simpa [prefixWord, tailWord_5175155, baseEnd_5175155] using wordTrace_append hprefix tailTrace_5175155
  have hstable : (prefixWord ++ tailWord_5175155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175155).length < 2 ^ (prefixWord ++ tailWord_5175155).sum := by decide
  have hdescent : baseEnd_5175155 < baseStart_5175155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175162 : List Nat := [3, 1, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_5175162 : Nat := 118140960795 + 5175162 * 2 ^ 59
def prefixEnd_5175162 : Nat := 4983230072969 + 3 ^ 40 * 5175162 * 2
def baseEnd_5175162 : Nat := 885781856961128796191623

theorem tailTrace_5175162 : CollatzResearch.WordTrace tailWord_5175162 prefixEnd_5175162 885781856961128796191623 := by
  unfold tailWord_5175162
  simp only [CollatzResearch.WordTrace]
  refine ⟨47188416219319849037007935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125835776584852930765354493 47188416219319849037007935)
  ·
    refine ⟨70782624328979773555511903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47188416219319849037007935 70782624328979773555511903)
    ·
      refine ⟨106173936493469660333267855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70782624328979773555511903 106173936493469660333267855)
      ·
        refine ⟨159260904740204490499901783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106173936493469660333267855 159260904740204490499901783)
        ·
          refine ⟨238891357110306735749852675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159260904740204490499901783 238891357110306735749852675)
          ·
            refine ⟨358337035665460103624779013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238891357110306735749852675 358337035665460103624779013)
            ·
              refine ⟨67188194187273769429646065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 358337035665460103624779013 67188194187273769429646065)
              ·
                refine ⟨50391145640455327072234549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67188194187273769429646065 50391145640455327072234549)
                ·
                  refine ⟨4724169903792686913021989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50391145640455327072234549 4724169903792686913021989)
                  ·
                    refine ⟨885781856961128796191623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724169903792686913021989 885781856961128796191623)
                    ·
                      rfl

theorem cell23_5175162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_5175162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175162 prefixEnd_5175162 := by exact prefixLift 5175162
  have htrace : WordTrace (prefixWord ++ tailWord_5175162) baseStart_5175162 baseEnd_5175162 := by
    simpa [prefixWord, tailWord_5175162, baseEnd_5175162] using wordTrace_append hprefix tailTrace_5175162
  have hstable : (prefixWord ++ tailWord_5175162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175162).length < 2 ^ (prefixWord ++ tailWord_5175162).sum := by decide
  have hdescent : baseEnd_5175162 < baseStart_5175162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175166 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5175166 : Nat := 118140960795 + 5175166 * 2 ^ 59
def prefixEnd_5175166 : Nat := 4983230072969 + 3 ^ 40 * 5175166 * 2
def baseEnd_5175166 : Nat := 885782541602001457641617

theorem tailTrace_5175166 : CollatzResearch.WordTrace tailWord_5175166 prefixEnd_5175166 885782541602001457641617 := by
  unfold tailWord_5175166
  simp only [CollatzResearch.WordTrace]
  refine ⟨23594226346158113103897169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125835873846176603220784901 23594226346158113103897169)
  ·
    refine ⟨17695669759618584827922877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23594226346158113103897169 17695669759618584827922877)
    ·
      refine ⟨6635876159856969310471079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17695669759618584827922877 6635876159856969310471079)
      ·
        refine ⟨9953814239785453965706619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6635876159856969310471079 9953814239785453965706619)
        ·
          refine ⟨14930721359678180948559929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9953814239785453965706619 14930721359678180948559929)
          ·
            refine ⟨11198041019758635711419947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14930721359678180948559929 11198041019758635711419947)
            ·
              refine ⟨16797061529637953567129921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11198041019758635711419947 16797061529637953567129921)
              ·
                refine ⟨12597796147228465175347441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16797061529637953567129921 12597796147228465175347441)
                ·
                  refine ⟨9448347110421348881510581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12597796147228465175347441 9448347110421348881510581)
                  ·
                    refine ⟨885782541602001457641617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9448347110421348881510581 885782541602001457641617)
                    ·
                      rfl

theorem cell23_5175166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5175166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175166 prefixEnd_5175166 := by exact prefixLift 5175166
  have htrace : WordTrace (prefixWord ++ tailWord_5175166) baseStart_5175166 baseEnd_5175166 := by
    simpa [prefixWord, tailWord_5175166, baseEnd_5175166] using wordTrace_append hprefix tailTrace_5175166
  have hstable : (prefixWord ++ tailWord_5175166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175166).length < 2 ^ (prefixWord ++ tailWord_5175166).sum := by decide
  have hdescent : baseEnd_5175166 < baseStart_5175166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175230 : List Nat := [4, 2, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_5175230 : Nat := 118140960795 + 5175230 * 2 ^ 59
def prefixEnd_5175230 : Nat := 4983230072969 + 3 ^ 40 * 5175230 * 2
def baseEnd_5175230 : Nat := 885793495855964040841519

theorem tailTrace_5175230 : CollatzResearch.WordTrace tailWord_5175230 prefixEnd_5175230 885793495855964040841519 := by
  unfold tailWord_5175230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23594518130129130470188393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125837430027355362507671429 23594518130129130470188393)
  ·
    refine ⟨17695888597596847852641295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23594518130129130470188393 17695888597596847852641295)
    ·
      refine ⟨26543832896395271778961943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17695888597596847852641295 26543832896395271778961943)
      ·
        refine ⟨39815749344592907668442915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26543832896395271778961943 39815749344592907668442915)
        ·
          refine ⟨59723624016889361502664373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39815749344592907668442915 59723624016889361502664373)
          ·
            refine ⟨5599089751583377640874785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59723624016889361502664373 5599089751583377640874785)
            ·
              refine ⟨4199317313687533230656089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5599089751583377640874785 4199317313687533230656089)
              ·
                refine ⟨3149487985265649922992067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4199317313687533230656089 3149487985265649922992067)
                ·
                  refine ⟨4724231977898474884488101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149487985265649922992067 4724231977898474884488101)
                  ·
                    refine ⟨885793495855964040841519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724231977898474884488101 885793495855964040841519)
                    ·
                      rfl

theorem cell23_5175230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_5175230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175230 prefixEnd_5175230 := by exact prefixLift 5175230
  have htrace : WordTrace (prefixWord ++ tailWord_5175230) baseStart_5175230 baseEnd_5175230 := by
    simpa [prefixWord, tailWord_5175230, baseEnd_5175230] using wordTrace_append hprefix tailTrace_5175230
  have hstable : (prefixWord ++ tailWord_5175230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175230).length < 2 ^ (prefixWord ++ tailWord_5175230).sum := by decide
  have hdescent : baseEnd_5175230 < baseStart_5175230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175263 : List Nat := [1, 1, 2, 3, 4, 3, 1, 1, 2, 3, 2]
def baseStart_5175263 : Nat := 118140960795 + 5175263 * 2 ^ 59
def prefixEnd_5175263 : Nat := 4983230072969 + 3 ^ 40 * 5175263 * 2
def baseEnd_5175263 : Nat := 2657397432429490493411905

theorem tailTrace_5175263 : CollatzResearch.WordTrace tailWord_5175263 prefixEnd_5175263 2657397432429490493411905 := by
  unfold tailWord_5175263
  simp only [CollatzResearch.WordTrace]
  refine ⟨188757348649913490397458443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125838232433275660264972295 188757348649913490397458443)
  ·
    refine ⟨283136022974870235596187665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188757348649913490397458443 283136022974870235596187665)
    ·
      refine ⟨212352017231152676697140749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283136022974870235596187665 212352017231152676697140749)
      ·
        refine ⟨79632006461682253761427781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212352017231152676697140749 79632006461682253761427781)
        ·
          refine ⟨14931001211565422580267709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79632006461682253761427781 14931001211565422580267709)
          ·
            refine ⟨5599125454337033467600391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14931001211565422580267709 5599125454337033467600391)
            ·
              refine ⟨8398688181505550201400587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5599125454337033467600391 8398688181505550201400587)
              ·
                refine ⟨12598032272258325302100881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8398688181505550201400587 12598032272258325302100881)
                ·
                  refine ⟨9448524204193743976575661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12598032272258325302100881 9448524204193743976575661)
                  ·
                    refine ⟨3543196576572653991215873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9448524204193743976575661 3543196576572653991215873)
                    ·
                      refine ⟨2657397432429490493411905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543196576572653991215873 2657397432429490493411905)
                      ·
                        rfl

theorem cell23_5175263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_5175263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175263 prefixEnd_5175263 := by exact prefixLift 5175263
  have htrace : WordTrace (prefixWord ++ tailWord_5175263) baseStart_5175263 baseEnd_5175263 := by
    simpa [prefixWord, tailWord_5175263, baseEnd_5175263] using wordTrace_append hprefix tailTrace_5175263
  have hstable : (prefixWord ++ tailWord_5175263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175263).length < 2 ^ (prefixWord ++ tailWord_5175263).sum := by decide
  have hdescent : baseEnd_5175263 < baseStart_5175263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175272 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_5175272 : Nat := 118140960795 + 5175272 * 2 ^ 59
def prefixEnd_5175272 : Nat := 4983230072969 + 3 ^ 40 * 5175272 * 2
def baseEnd_5175272 : Nat := 2657402053755380958199363

theorem tailTrace_5175272 : CollatzResearch.WordTrace tailWord_5175272 prefixEnd_5175272 2657402053755380958199363 := by
  unfold tailWord_5175272
  simp only [CollatzResearch.WordTrace]
  refine ⟨94378838453440442467268035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125838451271253923289690713 94378838453440442467268035)
  ·
    refine ⟨141568257680160663700902053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94378838453440442467268035 141568257680160663700902053)
    ·
      refine ⟨26544048315030124443919135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 141568257680160663700902053 26544048315030124443919135)
      ·
        refine ⟨39816072472545186665878703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26544048315030124443919135 39816072472545186665878703)
        ·
          refine ⟨59724108708817779998818055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39816072472545186665878703 59724108708817779998818055)
          ·
            refine ⟨89586163063226669998227083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59724108708817779998818055 89586163063226669998227083)
            ·
              refine ⟨134379244594840004997340625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89586163063226669998227083 134379244594840004997340625)
              ·
                refine ⟨100784433446130003748005469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134379244594840004997340625 100784433446130003748005469)
                ·
                  refine ⟨37794162542298751405502051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100784433446130003748005469 37794162542298751405502051)
                  ·
                    refine ⟨56691243813448127108253077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37794162542298751405502051 56691243813448127108253077)
                    ·
                      refine ⟨2657402053755380958199363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56691243813448127108253077 2657402053755380958199363)
                      ·
                        rfl

theorem cell23_5175272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_5175272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175272 prefixEnd_5175272 := by exact prefixLift 5175272
  have htrace : WordTrace (prefixWord ++ tailWord_5175272) baseStart_5175272 baseEnd_5175272 := by
    simpa [prefixWord, tailWord_5175272, baseEnd_5175272] using wordTrace_append hprefix tailTrace_5175272
  have hstable : (prefixWord ++ tailWord_5175272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175272).length < 2 ^ (prefixWord ++ tailWord_5175272).sum := by decide
  have hdescent : baseEnd_5175272 < baseStart_5175272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175303 : List Nat := [1, 1, 4, 3, 1, 3, 3, 1, 2, 4]
def baseStart_5175303 : Nat := 118140960795 + 5175303 * 2 ^ 59
def prefixEnd_5175303 : Nat := 4983230072969 + 3 ^ 40 * 5175303 * 2
def baseEnd_5175303 : Nat := 885805990551890112303907

theorem tailTrace_5175303 : CollatzResearch.WordTrace tailWord_5175303 prefixEnd_5175303 885805990551890112303907 := by
  unfold tailWord_5175303
  simp only [CollatzResearch.WordTrace]
  refine ⟨188758807569768577228914563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125839205046512384819276375 188758807569768577228914563)
  ·
    refine ⟨283138211354652865843371845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188758807569768577228914563 283138211354652865843371845)
    ·
      refine ⟨53088414628997412345632221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283138211354652865843371845 53088414628997412345632221)
      ·
        refine ⟨19908155485874029629612083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53088414628997412345632221 19908155485874029629612083)
        ·
          refine ⟨29862233228811044444418125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19908155485874029629612083 29862233228811044444418125)
          ·
            refine ⟨11198337460804141666656797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29862233228811044444418125 11198337460804141666656797)
            ·
              refine ⟨4199376547801553124996299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11198337460804141666656797 4199376547801553124996299)
              ·
                refine ⟨6299064821702329687494449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4199376547801553124996299 6299064821702329687494449)
                ·
                  refine ⟨4724298616276747265620837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6299064821702329687494449 4724298616276747265620837)
                  ·
                    refine ⟨885805990551890112303907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724298616276747265620837 885805990551890112303907)
                    ·
                      rfl

theorem cell23_5175303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_5175303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175303 prefixEnd_5175303 := by exact prefixLift 5175303
  have htrace : WordTrace (prefixWord ++ tailWord_5175303) baseStart_5175303 baseEnd_5175303 := by
    simpa [prefixWord, tailWord_5175303, baseEnd_5175303] using wordTrace_append hprefix tailTrace_5175303
  have hstable : (prefixWord ++ tailWord_5175303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175303).length < 2 ^ (prefixWord ++ tailWord_5175303).sum := by decide
  have hdescent : baseEnd_5175303 < baseStart_5175303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175360 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 2, 1, 3]
def baseStart_5175360 : Nat := 118140960795 + 5175360 * 2 ^ 59
def prefixEnd_5175360 : Nat := 4983230072969 + 3 ^ 40 * 5175360 * 2
def baseEnd_5175360 : Nat := 2657447240052976613898959

theorem tailTrace_5175360 : CollatzResearch.WordTrace tailWord_5175360 prefixEnd_5175360 2657447240052976613898959 := by
  unfold tailWord_5175360
  simp only [CollatzResearch.WordTrace]
  refine ⟨94380443265281037981869767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125840591020374717309159689 94380443265281037981869767)
  ·
    refine ⟨141570664897921556972804651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94380443265281037981869767 141570664897921556972804651)
    ·
      refine ⟨212355997346882335459206977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141570664897921556972804651 212355997346882335459206977)
      ·
        refine ⟨159266998010161751594405233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212355997346882335459206977 159266998010161751594405233)
        ·
          refine ⟨119450248507621313695803925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159266998010161751594405233 119450248507621313695803925)
          ·
            refine ⟨5599230398794749079490809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119450248507621313695803925 5599230398794749079490809)
            ·
              refine ⟨4199422799096061809618107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5599230398794749079490809 4199422799096061809618107)
              ·
                refine ⟨6299134198644092714427161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4199422799096061809618107 6299134198644092714427161)
                ·
                  refine ⟨4724350648983069535820371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6299134198644092714427161 4724350648983069535820371)
                  ·
                    refine ⟨7086525973474604303730557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4724350648983069535820371 7086525973474604303730557)
                    ·
                      refine ⟨2657447240052976613898959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7086525973474604303730557 2657447240052976613898959)
                      ·
                        rfl

theorem cell23_5175360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_5175360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175360 prefixEnd_5175360 := by exact prefixLift 5175360
  have htrace : WordTrace (prefixWord ++ tailWord_5175360) baseStart_5175360 baseEnd_5175360 := by
    simpa [prefixWord, tailWord_5175360, baseEnd_5175360] using wordTrace_append hprefix tailTrace_5175360
  have hstable : (prefixWord ++ tailWord_5175360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175360).length < 2 ^ (prefixWord ++ tailWord_5175360).sum := by decide
  have hdescent : baseEnd_5175360 < baseStart_5175360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175490 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5175490 : Nat := 118140960795 + 5175490 * 2 ^ 59
def prefixEnd_5175490 : Nat := 4983230072969 + 3 ^ 40 * 5175490 * 2
def baseEnd_5175490 : Nat := 2657513992538061105273361

theorem tailTrace_5175490 : CollatzResearch.WordTrace tailWord_5175490 prefixEnd_5175490 2657513992538061105273361 := by
  unfold tailWord_5175490
  simp only [CollatzResearch.WordTrace]
  refine ⟨47191407005022777041492981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125843752013394072110647949 47191407005022777041492981)
  ·
    refine ⟨4424194406720885347639967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47191407005022777041492981 4424194406720885347639967)
    ·
      refine ⟨6636291610081328021459951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4424194406720885347639967 6636291610081328021459951)
      ·
        refine ⟨9954437415121992032189927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6636291610081328021459951 9954437415121992032189927)
        ·
          refine ⟨14931656122682988048284891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9954437415121992032189927 14931656122682988048284891)
          ·
            refine ⟨22397484184024482072427337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14931656122682988048284891 22397484184024482072427337)
            ·
              refine ⟨16798113138018361554320503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22397484184024482072427337 16798113138018361554320503)
              ·
                refine ⟨25197169707027542331480755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16798113138018361554320503 25197169707027542331480755)
                ·
                  refine ⟨37795754560541313497221133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25197169707027542331480755 37795754560541313497221133)
                  ·
                    refine ⟨14173407960202992561457925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37795754560541313497221133 14173407960202992561457925)
                    ·
                      refine ⟨2657513992538061105273361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14173407960202992561457925 2657513992538061105273361)
                      ·
                        rfl

theorem cell23_5175490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5175490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175490 prefixEnd_5175490 := by exact prefixLift 5175490
  have htrace : WordTrace (prefixWord ++ tailWord_5175490) baseStart_5175490 baseEnd_5175490 := by
    simpa [prefixWord, tailWord_5175490, baseEnd_5175490] using wordTrace_append hprefix tailTrace_5175490
  have hstable : (prefixWord ++ tailWord_5175490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175490).length < 2 ^ (prefixWord ++ tailWord_5175490).sum := by decide
  have hdescent : baseEnd_5175490 < baseStart_5175490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175510 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_5175510 : Nat := 118140960795 + 5175510 * 2 ^ 59
def prefixEnd_5175510 : Nat := 4983230072969 + 3 ^ 40 * 5175510 * 2
def baseEnd_5175510 : Nat := 2657524262151151027023269

theorem tailTrace_5175510 : CollatzResearch.WordTrace tailWord_5175510 prefixEnd_5175510 2657524262151151027023269 := by
  unfold tailWord_5175510
  simp only [CollatzResearch.WordTrace]
  refine ⟨11797897342501165723856249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125844238320012434387799989 11797897342501165723856249)
  ·
    refine ⟨8848423006875874292892187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11797897342501165723856249 8848423006875874292892187)
    ·
      refine ⟨13272634510313811439338281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8848423006875874292892187 13272634510313811439338281)
      ·
        refine ⟨9954475882735358579503711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13272634510313811439338281 9954475882735358579503711)
        ·
          refine ⟨14931713824103037869255567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9954475882735358579503711 14931713824103037869255567)
          ·
            refine ⟨22397570736154556803883351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14931713824103037869255567 22397570736154556803883351)
            ·
              refine ⟨33596356104231835205825027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22397570736154556803883351 33596356104231835205825027)
              ·
                refine ⟨50394534156347752808737541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33596356104231835205825027 50394534156347752808737541)
                ·
                  refine ⟨9448975154315203651638289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50394534156347752808737541 9448975154315203651638289)
                  ·
                    refine ⟨7086731365736402738728717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9448975154315203651638289 7086731365736402738728717)
                    ·
                      refine ⟨2657524262151151027023269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7086731365736402738728717 2657524262151151027023269)
                      ·
                        rfl

theorem cell23_5175510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_5175510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175510 prefixEnd_5175510 := by exact prefixLift 5175510
  have htrace : WordTrace (prefixWord ++ tailWord_5175510) baseStart_5175510 baseEnd_5175510 := by
    simpa [prefixWord, tailWord_5175510, baseEnd_5175510] using wordTrace_append hprefix tailTrace_5175510
  have hstable : (prefixWord ++ tailWord_5175510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175510).length < 2 ^ (prefixWord ++ tailWord_5175510).sum := by decide
  have hdescent : baseEnd_5175510 < baseStart_5175510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175519 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_5175519 : Nat := 118140960795 + 5175519 * 2 ^ 59
def prefixEnd_5175519 : Nat := 4983230072969 + 3 ^ 40 * 5175519 * 2
def baseEnd_5175519 : Nat := 2657528883477041491810727

theorem tailTrace_5175519 : CollatzResearch.WordTrace tailWord_5175519 prefixEnd_5175519 2657528883477041491810727 := by
  unfold tailWord_5175519
  simp only [CollatzResearch.WordTrace]
  refine ⟨188766685736986046118777611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125844457157990697412518407 188766685736986046118777611)
  ·
    refine ⟨283150028605479069178166417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188766685736986046118777611 283150028605479069178166417)
    ·
      refine ⟨212362521454109301883624813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283150028605479069178166417 212362521454109301883624813)
      ·
        refine ⟨79635945545290988206359305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212362521454109301883624813 79635945545290988206359305)
        ·
          refine ⟨59726959158968241154769479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79635945545290988206359305 59726959158968241154769479)
          ·
            refine ⟨89590438738452361732154219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59726959158968241154769479 89590438738452361732154219)
            ·
              refine ⟨134385658107678542598231329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89590438738452361732154219 134385658107678542598231329)
              ·
                refine ⟨100789243580758906948673497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134385658107678542598231329 100789243580758906948673497)
                ·
                  refine ⟨75591932685569180211505123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100789243580758906948673497 75591932685569180211505123)
                  ·
                    refine ⟨113387899028353770317257685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75591932685569180211505123 113387899028353770317257685)
                    ·
                      refine ⟨2657528883477041491810727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 113387899028353770317257685 2657528883477041491810727)
                      ·
                        rfl

theorem cell23_5175519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_5175519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175519 prefixEnd_5175519 := by exact prefixLift 5175519
  have htrace : WordTrace (prefixWord ++ tailWord_5175519) baseStart_5175519 baseEnd_5175519 := by
    simpa [prefixWord, tailWord_5175519, baseEnd_5175519] using wordTrace_append hprefix tailTrace_5175519
  have hstable : (prefixWord ++ tailWord_5175519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175519).length < 2 ^ (prefixWord ++ tailWord_5175519).sum := by decide
  have hdescent : baseEnd_5175519 < baseStart_5175519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175560 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 1, 5]
def baseStart_5175560 : Nat := 118140960795 + 5175560 * 2 ^ 59
def prefixEnd_5175560 : Nat := 4983230072969 + 3 ^ 40 * 5175560 * 2
def baseEnd_5175560 : Nat := 885849978727958610466013

theorem tailTrace_5175560 : CollatzResearch.WordTrace tailWord_5175560 prefixEnd_5175560 885849978727958610466013 := by
  unfold tailWord_5175560
  simp only [CollatzResearch.WordTrace]
  refine ⟨94384090564918755060510067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125845454086558340080680089 94384090564918755060510067)
  ·
    refine ⟨141576135847378132590765101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94384090564918755060510067 141576135847378132590765101)
    ·
      refine ⟨53091050942766799721536913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141576135847378132590765101 53091050942766799721536913)
      ·
        refine ⟨39818288207075099791152685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53091050942766799721536913 39818288207075099791152685)
        ·
          refine ⟨14931858077653162421682257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39818288207075099791152685 14931858077653162421682257)
          ·
            refine ⟨11198893558239871816261693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14931858077653162421682257 11198893558239871816261693)
            ·
              refine ⟨4199585084339951931098135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11198893558239871816261693 4199585084339951931098135)
              ·
                refine ⟨6299377626509927896647203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4199585084339951931098135 6299377626509927896647203)
                ·
                  refine ⟨9449066439764891844970805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6299377626509927896647203 9449066439764891844970805)
                  ·
                    refine ⟨885849978727958610466013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9449066439764891844970805 885849978727958610466013)
                    ·
                      rfl

theorem cell23_5175560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_5175560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175560 prefixEnd_5175560 := by exact prefixLift 5175560
  have htrace : WordTrace (prefixWord ++ tailWord_5175560) baseStart_5175560 baseEnd_5175560 := by
    simpa [prefixWord, tailWord_5175560, baseEnd_5175560] using wordTrace_append hprefix tailTrace_5175560
  have hstable : (prefixWord ++ tailWord_5175560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175560).length < 2 ^ (prefixWord ++ tailWord_5175560).sum := by decide
  have hdescent : baseEnd_5175560 < baseStart_5175560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175569 : List Nat := [1, 2, 2, 1, 1, 16]
def baseStart_5175569 : Nat := 118140960795 + 5175569 * 2 ^ 59
def prefixEnd_5175569 : Nat := 4983230072969 + 3 ^ 40 * 5175569 * 2
def baseEnd_5175569 : Nat := 10936438508270643194179

theorem tailTrace_5175569 : CollatzResearch.WordTrace tailWord_5175569 prefixEnd_5175569 10936438508270643194179 := by
  unfold tailWord_5175569
  simp only [CollatzResearch.WordTrace]
  refine ⟨188768509386804904658097761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125845672924536603105398507 188768509386804904658097761)
  ·
    refine ⟨141576382040103678493573321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188768509386804904658097761 141576382040103678493573321)
    ·
      refine ⟨106182286530077758870179991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141576382040103678493573321 106182286530077758870179991)
      ·
        refine ⟨159273429795116638305269987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106182286530077758870179991 159273429795116638305269987)
        ·
          refine ⟨238910144692674957457904981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159273429795116638305269987 238910144692674957457904981)
          ·
            refine ⟨10936438508270643194179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 16 238910144692674957457904981 10936438508270643194179)
            ·
              rfl

theorem cell23_5175569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 16].length) (baseStart_5175569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175569 prefixEnd_5175569 := by exact prefixLift 5175569
  have htrace : WordTrace (prefixWord ++ tailWord_5175569) baseStart_5175569 baseEnd_5175569 := by
    simpa [prefixWord, tailWord_5175569, baseEnd_5175569] using wordTrace_append hprefix tailTrace_5175569
  have hstable : (prefixWord ++ tailWord_5175569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175569).length < 2 ^ (prefixWord ++ tailWord_5175569).sum := by decide
  have hdescent : baseEnd_5175569 < baseStart_5175569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175573 : List Nat := [1, 3, 2, 1, 2, 1, 3, 4, 2, 4]
def baseStart_5175573 : Nat := 118140960795 + 5175573 * 2 ^ 59
def prefixEnd_5175573 : Nat := 4983230072969 + 3 ^ 40 * 5175573 * 2
def baseEnd_5175573 : Nat := 885852203810794760178493

theorem tailTrace_5175573 : CollatzResearch.WordTrace tailWord_5175573 prefixEnd_5175573 885852203810794760178493 := by
  unfold tailWord_5175573
  simp only [CollatzResearch.WordTrace]
  refine ⟨188768655278790413341243373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125845770185860275560828915 188768655278790413341243373)
  ·
    refine ⟨70788245729546405002966265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188768655278790413341243373 70788245729546405002966265)
    ·
      refine ⟨53091184297159803752224699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70788245729546405002966265 53091184297159803752224699)
      ·
        refine ⟨79636776445739705628337049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53091184297159803752224699 79636776445739705628337049)
        ·
          refine ⟨59727582334304779221252787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79636776445739705628337049 59727582334304779221252787)
          ·
            refine ⟨89591373501457168831879181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59727582334304779221252787 89591373501457168831879181)
            ·
              refine ⟨33596765063046438311954693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89591373501457168831879181 33596765063046438311954693)
              ·
                refine ⟨6299393449321207183491505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33596765063046438311954693 6299393449321207183491505)
                ·
                  refine ⟨4724545086990905387618629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6299393449321207183491505 4724545086990905387618629)
                  ·
                    refine ⟨885852203810794760178493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724545086990905387618629 885852203810794760178493)
                    ·
                      rfl

theorem cell23_5175573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_5175573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175573 prefixEnd_5175573 := by exact prefixLift 5175573
  have htrace : WordTrace (prefixWord ++ tailWord_5175573) baseStart_5175573 baseEnd_5175573 := by
    simpa [prefixWord, tailWord_5175573, baseEnd_5175573] using wordTrace_append hprefix tailTrace_5175573
  have hstable : (prefixWord ++ tailWord_5175573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175573).length < 2 ^ (prefixWord ++ tailWord_5175573).sum := by decide
  have hdescent : baseEnd_5175573 < baseStart_5175573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175576 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5175576 : Nat := 118140960795 + 5175576 * 2 ^ 59
def prefixEnd_5175576 : Nat := 4983230072969 + 3 ^ 40 * 5175576 * 2
def baseEnd_5175576 : Nat := 2657558151874347768797965

theorem tailTrace_5175576 : CollatzResearch.WordTrace tailWord_5175576 prefixEnd_5175576 2657558151874347768797965 := by
  unfold tailWord_5175576
  simp only [CollatzResearch.WordTrace]
  refine ⟨94384382348889772426801291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125845843131853029902401721 94384382348889772426801291)
  ·
    refine ⟨141576573523334658640201937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94384382348889772426801291 141576573523334658640201937)
    ·
      refine ⟨106182430142500993980151453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141576573523334658640201937 106182430142500993980151453)
      ·
        refine ⟨39818411303437872742556795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106182430142500993980151453 39818411303437872742556795)
        ·
          refine ⟨59727616955156809113835193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39818411303437872742556795 59727616955156809113835193)
          ·
            refine ⟨44795712716367606835376395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59727616955156809113835193 44795712716367606835376395)
            ·
              refine ⟨67193569074551410253064593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44795712716367606835376395 67193569074551410253064593)
              ·
                refine ⟨50395176805913557689798445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67193569074551410253064593 50395176805913557689798445)
                ·
                  refine ⟨18898191302217584133674417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50395176805913557689798445 18898191302217584133674417)
                  ·
                    refine ⟨14173643476663188100255813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18898191302217584133674417 14173643476663188100255813)
                    ·
                      refine ⟨2657558151874347768797965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14173643476663188100255813 2657558151874347768797965)
                      ·
                        rfl

theorem cell23_5175576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5175576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175576 prefixEnd_5175576 := by exact prefixLift 5175576
  have htrace : WordTrace (prefixWord ++ tailWord_5175576) baseStart_5175576 baseEnd_5175576 := by
    simpa [prefixWord, tailWord_5175576, baseEnd_5175576] using wordTrace_append hprefix tailTrace_5175576
  have hstable : (prefixWord ++ tailWord_5175576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175576).length < 2 ^ (prefixWord ++ tailWord_5175576).sum := by decide
  have hdescent : baseEnd_5175576 < baseStart_5175576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175580 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_5175580 : Nat := 118140960795 + 5175580 * 2 ^ 59
def prefixEnd_5175580 : Nat := 4983230072969 + 3 ^ 40 * 5175580 * 2
def baseEnd_5175580 : Nat := 2657560205796965753147947

theorem tailTrace_5175580 : CollatzResearch.WordTrace tailWord_5175580 prefixEnd_5175580 2657560205796965753147947 := by
  unfold tailWord_5175580
  simp only [CollatzResearch.WordTrace]
  refine ⟨94384455294882526768374097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125845940393176702357832129 94384455294882526768374097)
  ·
    refine ⟨70788341471161895076280573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94384455294882526768374097 70788341471161895076280573)
    ·
      refine ⟨26545628051685710653605215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70788341471161895076280573 26545628051685710653605215)
      ·
        refine ⟨39818442077528565980407823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26545628051685710653605215 39818442077528565980407823)
        ·
          refine ⟨59727663116292848970611735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39818442077528565980407823 59727663116292848970611735)
          ·
            refine ⟨89591494674439273455917603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59727663116292848970611735 89591494674439273455917603)
            ·
              refine ⟨134387242011658910183876405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89591494674439273455917603 134387242011658910183876405)
              ·
                refine ⟨12598803938593022829738413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134387242011658910183876405 12598803938593022829738413)
                ·
                  refine ⟨4724551476972383561151905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12598803938593022829738413 4724551476972383561151905)
                  ·
                    refine ⟨3543413607729287670863929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4724551476972383561151905 3543413607729287670863929)
                    ·
                      refine ⟨2657560205796965753147947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543413607729287670863929 2657560205796965753147947)
                      ·
                        rfl

theorem cell23_5175580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_5175580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175580 prefixEnd_5175580 := by exact prefixLift 5175580
  have htrace : WordTrace (prefixWord ++ tailWord_5175580) baseStart_5175580 baseEnd_5175580 := by
    simpa [prefixWord, tailWord_5175580, baseEnd_5175580] using wordTrace_append hprefix tailTrace_5175580
  have hstable : (prefixWord ++ tailWord_5175580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175580).length < 2 ^ (prefixWord ++ tailWord_5175580).sum := by decide
  have hdescent : baseEnd_5175580 < baseStart_5175580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175583 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 3]
def baseStart_5175583 : Nat := 118140960795 + 5175583 * 2 ^ 59
def prefixEnd_5175583 : Nat := 4983230072969 + 3 ^ 40 * 5175583 * 2
def baseEnd_5175583 : Nat := 2657561746238929241410433

theorem tailTrace_5175583 : CollatzResearch.WordTrace tailWord_5175583 prefixEnd_5175583 2657561746238929241410433 := by
  unfold tailWord_5175583
  simp only [CollatzResearch.WordTrace]
  refine ⟨188769020008754185049107403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125846013339169456699404935 188769020008754185049107403)
  ·
    refine ⟨283153530013131277573661105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188769020008754185049107403 283153530013131277573661105)
    ·
      refine ⟨212365147509848458180245829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283153530013131277573661105 212365147509848458180245829)
      ·
        refine ⟨39818465158096585908796093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212365147509848458180245829 39818465158096585908796093)
        ·
          refine ⟨14931924434286219715798535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39818465158096585908796093 14931924434286219715798535)
          ·
            refine ⟨22397886651429329573697803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14931924434286219715798535 22397886651429329573697803)
            ·
              refine ⟨33596829977143994360546705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22397886651429329573697803 33596829977143994360546705)
              ·
                refine ⟨25197622482857995770410029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33596829977143994360546705 25197622482857995770410029)
                ·
                  refine ⟨9449108431071748413903761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25197622482857995770410029 9449108431071748413903761)
                  ·
                    refine ⟨7086831323303811310427821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9449108431071748413903761 7086831323303811310427821)
                    ·
                      refine ⟨2657561746238929241410433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7086831323303811310427821 2657561746238929241410433)
                      ·
                        rfl

theorem cell23_5175583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_5175583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175583 prefixEnd_5175583 := by exact prefixLift 5175583
  have htrace : WordTrace (prefixWord ++ tailWord_5175583) baseStart_5175583 baseEnd_5175583 := by
    simpa [prefixWord, tailWord_5175583, baseEnd_5175583] using wordTrace_append hprefix tailTrace_5175583
  have hstable : (prefixWord ++ tailWord_5175583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175583).length < 2 ^ (prefixWord ++ tailWord_5175583).sum := by decide
  have hdescent : baseEnd_5175583 < baseStart_5175583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175614 : List Nat := [4, 2, 1, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_5175614 : Nat := 118140960795 + 5175614 * 2 ^ 59
def prefixEnd_5175614 : Nat := 4983230072969 + 3 ^ 40 * 5175614 * 2
def baseEnd_5175614 : Nat := 2657577664139218620122791

theorem tailTrace_5175614 : CollatzResearch.WordTrace tailWord_5175614 prefixEnd_5175614 2657577664139218620122791 := by
  unfold tailWord_5175614
  simp only [CollatzResearch.WordTrace]
  refine ⟨23596268833955234667935737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125846767114427918228990597 23596268833955234667935737)
  ·
    refine ⟨17697201625466426000951803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23596268833955234667935737 17697201625466426000951803)
    ·
      refine ⟨26545802438199639001427705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17697201625466426000951803 26545802438199639001427705)
      ·
        refine ⟨19909351828649729251070779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26545802438199639001427705 19909351828649729251070779)
        ·
          refine ⟨29864027742974593876606169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19909351828649729251070779 29864027742974593876606169)
          ·
            refine ⟨22398020807230945407454627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29864027742974593876606169 22398020807230945407454627)
            ·
              refine ⟨33597031210846418111181941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22398020807230945407454627 33597031210846418111181941)
              ·
                refine ⟨3149721676016851697923307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33597031210846418111181941 3149721676016851697923307)
                ·
                  refine ⟨4724582514025277546884961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149721676016851697923307 4724582514025277546884961)
                  ·
                    refine ⟨3543436885518958160163721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4724582514025277546884961 3543436885518958160163721)
                    ·
                      refine ⟨2657577664139218620122791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543436885518958160163721 2657577664139218620122791)
                      ·
                        rfl

theorem cell23_5175614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_5175614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175614 prefixEnd_5175614 := by exact prefixLift 5175614
  have htrace : WordTrace (prefixWord ++ tailWord_5175614) baseStart_5175614 baseEnd_5175614 := by
    simpa [prefixWord, tailWord_5175614, baseEnd_5175614] using wordTrace_append hprefix tailTrace_5175614
  have hstable : (prefixWord ++ tailWord_5175614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175614).length < 2 ^ (prefixWord ++ tailWord_5175614).sum := by decide
  have hdescent : baseEnd_5175614 < baseStart_5175614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175617 : List Nat := [1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5175617 : Nat := 118140960795 + 5175617 * 2 ^ 59
def prefixEnd_5175617 : Nat := 4983230072969 + 3 ^ 40 * 5175617 * 2
def baseEnd_5175617 : Nat := 2657579204581182108385277

theorem tailTrace_5175617 : CollatzResearch.WordTrace tailWord_5175617 prefixEnd_5175617 2657579204581182108385277 := by
  unfold tailWord_5175617
  simp only [CollatzResearch.WordTrace]
  refine ⟨188770260090631008855845105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125846840060420672570563403 188770260090631008855845105)
  ·
    refine ⟨141577695067973256641883829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188770260090631008855845105 141577695067973256641883829)
    ·
      refine ⟨13272908912622492810176609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141577695067973256641883829 13272908912622492810176609)
      ·
        refine ⟨9954681684466869607632457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13272908912622492810176609 9954681684466869607632457)
        ·
          refine ⟨7466011263350152205724343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9954681684466869607632457 7466011263350152205724343)
          ·
            refine ⟨11199016895025228308586515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7466011263350152205724343 11199016895025228308586515)
            ·
              refine ⟨16798525342537842462879773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11199016895025228308586515 16798525342537842462879773)
              ·
                refine ⟨6299447003451690923579915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16798525342537842462879773 6299447003451690923579915)
                ·
                  refine ⟨9449170505177536385369873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6299447003451690923579915 9449170505177536385369873)
                  ·
                    refine ⟨7086877878883152289027405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9449170505177536385369873 7086877878883152289027405)
                    ·
                      refine ⟨2657579204581182108385277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7086877878883152289027405 2657579204581182108385277)
                      ·
                        rfl

theorem cell23_5175617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5175617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175617 prefixEnd_5175617 := by exact prefixLift 5175617
  have htrace : WordTrace (prefixWord ++ tailWord_5175617) baseStart_5175617 baseEnd_5175617 := by
    simpa [prefixWord, tailWord_5175617, baseEnd_5175617] using wordTrace_append hprefix tailTrace_5175617
  have hstable : (prefixWord ++ tailWord_5175617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175617).length < 2 ^ (prefixWord ++ tailWord_5175617).sum := by decide
  have hdescent : baseEnd_5175617 < baseStart_5175617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175630 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_5175630 : Nat := 118140960795 + 5175630 * 2 ^ 59
def prefixEnd_5175630 : Nat := 4983230072969 + 3 ^ 40 * 5175630 * 2
def baseEnd_5175630 : Nat := 2657585879829690557522717

theorem tailTrace_5175630 : CollatzResearch.WordTrace tailWord_5175630 prefixEnd_5175630 2657585879829690557522717 := by
  unfold tailWord_5175630
  simp only [CollatzResearch.WordTrace]
  refine ⟨23596341779947989009508543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125847156159722608050712229 23596341779947989009508543)
  ·
    refine ⟨35394512669921983514262815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23596341779947989009508543 35394512669921983514262815)
    ·
      refine ⟨53091769004882975271394223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35394512669921983514262815 53091769004882975271394223)
      ·
        refine ⟨79637653507324462907091335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53091769004882975271394223 79637653507324462907091335)
        ·
          refine ⟨119456480260986694360637003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79637653507324462907091335 119456480260986694360637003)
          ·
            refine ⟨179184720391480041540955505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119456480260986694360637003 179184720391480041540955505)
            ·
              refine ⟨134388540293610031155716629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179184720391480041540955505 134388540293610031155716629)
              ·
                refine ⟨6299462826262970210424217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134388540293610031155716629 6299462826262970210424217)
                ·
                  refine ⟨4724597119697227657818163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6299462826262970210424217 4724597119697227657818163)
                  ·
                    refine ⟨7086895679545841486727245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4724597119697227657818163 7086895679545841486727245)
                    ·
                      refine ⟨2657585879829690557522717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7086895679545841486727245 2657585879829690557522717)
                      ·
                        rfl

theorem cell23_5175630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_5175630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175630 prefixEnd_5175630 := by exact prefixLift 5175630
  have htrace : WordTrace (prefixWord ++ tailWord_5175630) baseStart_5175630 baseEnd_5175630 := by
    simpa [prefixWord, tailWord_5175630, baseEnd_5175630] using wordTrace_append hprefix tailTrace_5175630
  have hstable : (prefixWord ++ tailWord_5175630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175630).length < 2 ^ (prefixWord ++ tailWord_5175630).sum := by decide
  have hdescent : baseEnd_5175630 < baseStart_5175630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175644 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5175644 : Nat := 118140960795 + 5175644 * 2 ^ 59
def prefixEnd_5175644 : Nat := 4983230072969 + 3 ^ 40 * 5175644 * 2
def baseEnd_5175644 : Nat := 2657593068558853502747653

theorem tailTrace_5175644 : CollatzResearch.WordTrace tailWord_5175644 prefixEnd_5175644 2657593068558853502747653 := by
  unfold tailWord_5175644
  simp only [CollatzResearch.WordTrace]
  refine ⟨94385622430766596233538993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125847496574355461644718657 94385622430766596233538993)
  ·
    refine ⟨70789216823074947175154245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94385622430766596233538993 70789216823074947175154245)
    ·
      refine ⟨13272978154326552595341421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70789216823074947175154245 13272978154326552595341421)
      ·
        refine ⟨4977366807872457223253033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13272978154326552595341421 4977366807872457223253033)
        ·
          refine ⟨3733025105904342917439775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4977366807872457223253033 3733025105904342917439775)
          ·
            refine ⟨5599537658856514376159663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733025105904342917439775 5599537658856514376159663)
            ·
              refine ⟨8399306488284771564239495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5599537658856514376159663 8399306488284771564239495)
              ·
                refine ⟨12598959732427157346359243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8399306488284771564239495 12598959732427157346359243)
                ·
                  refine ⟨18898439598640736019538865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12598959732427157346359243 18898439598640736019538865)
                  ·
                    refine ⟨14173829698980552014654149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18898439598640736019538865 14173829698980552014654149)
                    ·
                      refine ⟨2657593068558853502747653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14173829698980552014654149 2657593068558853502747653)
                      ·
                        rfl

theorem cell23_5175644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5175644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175644 prefixEnd_5175644 := by exact prefixLift 5175644
  have htrace : WordTrace (prefixWord ++ tailWord_5175644) baseStart_5175644 baseEnd_5175644 := by
    simpa [prefixWord, tailWord_5175644, baseEnd_5175644] using wordTrace_append hprefix tailTrace_5175644
  have hstable : (prefixWord ++ tailWord_5175644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175644).length < 2 ^ (prefixWord ++ tailWord_5175644).sum := by decide
  have hdescent : baseEnd_5175644 < baseStart_5175644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175687 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_5175687 : Nat := 118140960795 + 5175687 * 2 ^ 59
def prefixEnd_5175687 : Nat := 4983230072969 + 3 ^ 40 * 5175687 * 2
def baseEnd_5175687 : Nat := 2657615148226996834509955

theorem tailTrace_5175687 : CollatzResearch.WordTrace tailWord_5175687 prefixEnd_5175687 2657615148226996834509955 := by
  unfold tailWord_5175687
  simp only [CollatzResearch.WordTrace]
  refine ⟨188772813200377410810893315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125848542133584940540595543 188772813200377410810893315)
  ·
    refine ⟨283159219800566116216339973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188772813200377410810893315 283159219800566116216339973)
    ·
      refine ⟨53092353712606146790563745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283159219800566116216339973 53092353712606146790563745)
      ·
        refine ⟨39819265284454610092922809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53092353712606146790563745 39819265284454610092922809)
        ·
          refine ⟨29864448963340957569692107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39819265284454610092922809 29864448963340957569692107)
          ·
            refine ⟨44796673445011436354538161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29864448963340957569692107 44796673445011436354538161)
            ·
              refine ⟨33597505083758577265903621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44796673445011436354538161 33597505083758577265903621)
              ·
                refine ⟨6299532203204733237356929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33597505083758577265903621 6299532203204733237356929)
                ·
                  refine ⟨4724649152403549928017697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6299532203204733237356929 4724649152403549928017697)
                  ·
                    refine ⟨3543486864302662446013273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4724649152403549928017697 3543486864302662446013273)
                    ·
                      refine ⟨2657615148226996834509955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543486864302662446013273 2657615148226996834509955)
                      ·
                        rfl

theorem cell23_5175687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_5175687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175687 prefixEnd_5175687 := by exact prefixLift 5175687
  have htrace : WordTrace (prefixWord ++ tailWord_5175687) baseStart_5175687 baseEnd_5175687 := by
    simpa [prefixWord, tailWord_5175687, baseEnd_5175687] using wordTrace_append hprefix tailTrace_5175687
  have hstable : (prefixWord ++ tailWord_5175687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175687).length < 2 ^ (prefixWord ++ tailWord_5175687).sum := by decide
  have hdescent : baseEnd_5175687 < baseStart_5175687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175703 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_5175703 : Nat := 118140960795 + 5175703 * 2 ^ 59
def prefixEnd_5175703 : Nat := 4983230072969 + 3 ^ 40 * 5175703 * 2
def baseEnd_5175703 : Nat := 2657623363917468771909881

theorem tailTrace_5175703 : CollatzResearch.WordTrace tailWord_5175703 prefixEnd_5175703 2657623363917468771909881 := by
  unfold tailWord_5175703
  simp only [CollatzResearch.WordTrace]
  refine ⟨188773396768319445543475763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125848931178879630362317175 188773396768319445543475763)
  ·
    refine ⟨283160095152479168315213645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188773396768319445543475763 283160095152479168315213645)
    ·
      refine ⟨106185035682179688118205117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283160095152479168315213645 106185035682179688118205117)
      ·
        refine ⟨39819388380817383044326919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106185035682179688118205117 39819388380817383044326919)
        ·
          refine ⟨59729082571226074566490379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39819388380817383044326919 59729082571226074566490379)
          ·
            refine ⟨89593623856839111849735569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59729082571226074566490379 89593623856839111849735569)
            ·
              refine ⟨67195217892629333887301677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89593623856839111849735569 67195217892629333887301677)
              ·
                refine ⟨25198206709736000207738129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67195217892629333887301677 25198206709736000207738129)
                ·
                  refine ⟨18898655032302000155803597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25198206709736000207738129 18898655032302000155803597)
                  ·
                    refine ⟨7086995637113250058426349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18898655032302000155803597 7086995637113250058426349)
                    ·
                      refine ⟨2657623363917468771909881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7086995637113250058426349 2657623363917468771909881)
                      ·
                        rfl

theorem cell23_5175703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_5175703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175703 prefixEnd_5175703 := by exact prefixLift 5175703
  have htrace : WordTrace (prefixWord ++ tailWord_5175703) baseStart_5175703 baseEnd_5175703 := by
    simpa [prefixWord, tailWord_5175703, baseEnd_5175703] using wordTrace_append hprefix tailTrace_5175703
  have hstable : (prefixWord ++ tailWord_5175703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175703).length < 2 ^ (prefixWord ++ tailWord_5175703).sum := by decide
  have hdescent : baseEnd_5175703 < baseStart_5175703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175704 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5175704 : Nat := 118140960795 + 5175704 * 2 ^ 59
def prefixEnd_5175704 : Nat := 4983230072969 + 3 ^ 40 * 5175704 * 2
def baseEnd_5175704 : Nat := 2657623877398123267997377

theorem tailTrace_5175704 : CollatzResearch.WordTrace tailWord_5175704 prefixEnd_5175704 2657623877398123267997377 := by
  unfold tailWord_5175704
  simp only [CollatzResearch.WordTrace]
  refine ⟨94386716620657911357131083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125848955494210548476174777 94386716620657911357131083)
  ·
    refine ⟨141580074930986867035696625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94386716620657911357131083 141580074930986867035696625)
    ·
      refine ⟨106185056198240150276772469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141580074930986867035696625 106185056198240150276772469)
      ·
        refine ⟨9954849018585014088447419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106185056198240150276772469 9954849018585014088447419)
        ·
          refine ⟨14932273527877521132671129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9954849018585014088447419 14932273527877521132671129)
          ·
            refine ⟨11199205145908140849503347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14932273527877521132671129 11199205145908140849503347)
            ·
              refine ⟨16798807718862211274255021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11199205145908140849503347 16798807718862211274255021)
              ·
                refine ⟨6299552894573329227845633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16798807718862211274255021 6299552894573329227845633)
                ·
                  refine ⟨4724664670929996920884225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6299552894573329227845633 4724664670929996920884225)
                  ·
                    refine ⟨3543498503197497690663169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4724664670929996920884225 3543498503197497690663169)
                    ·
                      refine ⟨2657623877398123267997377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543498503197497690663169 2657623877398123267997377)
                      ·
                        rfl

theorem cell23_5175704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5175704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175704 prefixEnd_5175704 := by exact prefixLift 5175704
  have htrace : WordTrace (prefixWord ++ tailWord_5175704) baseStart_5175704 baseEnd_5175704 := by
    simpa [prefixWord, tailWord_5175704, baseEnd_5175704] using wordTrace_append hprefix tailTrace_5175704
  have hstable : (prefixWord ++ tailWord_5175704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175704).length < 2 ^ (prefixWord ++ tailWord_5175704).sum := by decide
  have hdescent : baseEnd_5175704 < baseStart_5175704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175740 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 2, 5]
def baseStart_5175740 : Nat := 118140960795 + 5175740 * 2 ^ 59
def prefixEnd_5175740 : Nat := 4983230072969 + 3 ^ 40 * 5175740 * 2
def baseEnd_5175740 : Nat := 885880787567228375715737

theorem tailTrace_5175740 : CollatzResearch.WordTrace tailWord_5175740 prefixEnd_5175740 885880787567228375715737 := by
  unfold tailWord_5175740
  simp only [CollatzResearch.WordTrace]
  refine ⟨94387373134592700431286337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125849830846123600575048449 94387373134592700431286337)
  ·
    refine ⟨70790529850944525323464753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94387373134592700431286337 70790529850944525323464753)
    ·
      refine ⟨53092897388208393992598565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70790529850944525323464753 53092897388208393992598565)
      ·
        refine ⟨9954918260289073873612231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53092897388208393992598565 9954918260289073873612231)
        ·
          refine ⟨14932377390433610810418347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9954918260289073873612231 14932377390433610810418347)
          ·
            refine ⟨22398566085650416215627521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14932377390433610810418347 22398566085650416215627521)
            ·
              refine ⟨16798924564237812161720641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22398566085650416215627521 16798924564237812161720641)
              ·
                refine ⟨12599193423178359121290481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16798924564237812161720641 12599193423178359121290481)
                ·
                  refine ⟨9449395067383769340967861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12599193423178359121290481 9449395067383769340967861)
                  ·
                    refine ⟨885880787567228375715737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9449395067383769340967861 885880787567228375715737)
                    ·
                      rfl

theorem cell23_5175740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_5175740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175740 prefixEnd_5175740 := by exact prefixLift 5175740
  have htrace : WordTrace (prefixWord ++ tailWord_5175740) baseStart_5175740 baseEnd_5175740 := by
    simpa [prefixWord, tailWord_5175740, baseEnd_5175740] using wordTrace_append hprefix tailTrace_5175740
  have hstable : (prefixWord ++ tailWord_5175740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175740).length < 2 ^ (prefixWord ++ tailWord_5175740).sum := by decide
  have hdescent : baseEnd_5175740 < baseStart_5175740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175770 : List Nat := [3, 1, 1, 2, 3, 1, 3, 2, 3, 4]
def baseStart_5175770 : Nat := 118140960795 + 5175770 * 2 ^ 59
def prefixEnd_5175770 : Nat := 4983230072969 + 3 ^ 40 * 5175770 * 2
def baseEnd_5175770 : Nat := 885885922373773336590691

theorem tailTrace_5175770 : CollatzResearch.WordTrace tailWord_5175770 prefixEnd_5175770 885885922373773336590691 := by
  unfold tailWord_5175770
  simp only [CollatzResearch.WordTrace]
  refine ⟨47193960114769178996541191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125850560306051143990776509 47193960114769178996541191)
  ·
    refine ⟨70790940172153768494811787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47193960114769178996541191 70790940172153768494811787)
    ·
      refine ⟨106186410258230652742217681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70790940172153768494811787 106186410258230652742217681)
      ·
        refine ⟨79639807693672989556663261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106186410258230652742217681 79639807693672989556663261)
        ·
          refine ⟨29864927885127371083748723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79639807693672989556663261 29864927885127371083748723)
          ·
            refine ⟨44797391827691056625623085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29864927885127371083748723 44797391827691056625623085)
            ·
              refine ⟨16799021935384146234608657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44797391827691056625623085 16799021935384146234608657)
              ·
                refine ⟨12599266451538109675956493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16799021935384146234608657 12599266451538109675956493)
                ·
                  refine ⟨4724724919326791128483685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12599266451538109675956493 4724724919326791128483685)
                  ·
                    refine ⟨885885922373773336590691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724724919326791128483685 885885922373773336590691)
                    ·
                      rfl

theorem cell23_5175770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_5175770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175770 prefixEnd_5175770 := by exact prefixLift 5175770
  have htrace : WordTrace (prefixWord ++ tailWord_5175770) baseStart_5175770 baseEnd_5175770 := by
    simpa [prefixWord, tailWord_5175770, baseEnd_5175770] using wordTrace_append hprefix tailTrace_5175770
  have hstable : (prefixWord ++ tailWord_5175770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175770).length < 2 ^ (prefixWord ++ tailWord_5175770).sum := by decide
  have hdescent : baseEnd_5175770 < baseStart_5175770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175783 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 8]
def baseStart_5175783 : Nat := 118140960795 + 5175783 * 2 ^ 59
def prefixEnd_5175783 : Nat := 4983230072969 + 3 ^ 40 * 5175783 * 2
def baseEnd_5175783 : Nat := 295296049152203162101057

theorem tailTrace_5175783 : CollatzResearch.WordTrace tailWord_5175783 prefixEnd_5175783 295296049152203162101057 := by
  unfold tailWord_5175783
  simp only [CollatzResearch.WordTrace]
  refine ⟨188776314608029619206388003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125850876405353079470925335 188776314608029619206388003)
  ·
    refine ⟨283164471912044428809582005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188776314608029619206388003 283164471912044428809582005)
    ·
      refine ⟨26546669241754165200898313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 283164471912044428809582005 26546669241754165200898313)
      ·
        refine ⟨19910001931315623900673735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26546669241754165200898313 19910001931315623900673735)
        ·
          refine ⟨29865002896973435851010603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19910001931315623900673735 29865002896973435851010603)
          ·
            refine ⟨44797504345460153776515905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29865002896973435851010603 44797504345460153776515905)
            ·
              refine ⟨33598128259095115332386929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44797504345460153776515905 33598128259095115332386929)
              ·
                refine ⟨25198596194321336499290197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33598128259095115332386929 25198596194321336499290197)
                ·
                  refine ⟨295296049152203162101057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25198596194321336499290197 295296049152203162101057)
                  ·
                    rfl

theorem cell23_5175783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 8].length) (baseStart_5175783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175783 prefixEnd_5175783 := by exact prefixLift 5175783
  have htrace : WordTrace (prefixWord ++ tailWord_5175783) baseStart_5175783 baseEnd_5175783 := by
    simpa [prefixWord, tailWord_5175783, baseEnd_5175783] using wordTrace_append hprefix tailTrace_5175783
  have hstable : (prefixWord ++ tailWord_5175783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175783).length < 2 ^ (prefixWord ++ tailWord_5175783).sum := by decide
  have hdescent : baseEnd_5175783 < baseStart_5175783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175787 : List Nat := [1, 1, 1, 1, 2, 3, 6, 3, 1, 4]
def baseStart_5175787 : Nat := 118140960795 + 5175787 * 2 ^ 59
def prefixEnd_5175787 : Nat := 4983230072969 + 3 ^ 40 * 5175787 * 2
def baseEnd_5175787 : Nat := 885888832097482147753165

theorem tailTrace_5175787 : CollatzResearch.WordTrace tailWord_5175787 prefixEnd_5175787 885888832097482147753165 := by
  unfold tailWord_5175787
  simp only [CollatzResearch.WordTrace]
  refine ⟨188776460500015127889533615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125850973666676751926355743 188776460500015127889533615)
  ·
    refine ⟨283164690750022691834300423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188776460500015127889533615 283164690750022691834300423)
    ·
      refine ⟨424747036125034037751450635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283164690750022691834300423 424747036125034037751450635)
      ·
        refine ⟨637120554187551056627175953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424747036125034037751450635 637120554187551056627175953)
        ·
          refine ⟨477840415640663292470381965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637120554187551056627175953 477840415640663292470381965)
          ·
            refine ⟨179190155865248734676393237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 477840415640663292470381965 179190155865248734676393237)
            ·
              refine ⟨8399538556183534437955933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 179190155865248734676393237 8399538556183534437955933)
              ·
                refine ⟨3149826958568825414233475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8399538556183534437955933 3149826958568825414233475)
                ·
                  refine ⟨4724740437853238121350213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149826958568825414233475 4724740437853238121350213)
                  ·
                    refine ⟨885888832097482147753165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724740437853238121350213 885888832097482147753165)
                    ·
                      rfl

theorem cell23_5175787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 3, 1, 4].length) (baseStart_5175787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175787 prefixEnd_5175787 := by exact prefixLift 5175787
  have htrace : WordTrace (prefixWord ++ tailWord_5175787) baseStart_5175787 baseEnd_5175787 := by
    simpa [prefixWord, tailWord_5175787, baseEnd_5175787] using wordTrace_append hprefix tailTrace_5175787
  have hstable : (prefixWord ++ tailWord_5175787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175787).length < 2 ^ (prefixWord ++ tailWord_5175787).sum := by decide
  have hdescent : baseEnd_5175787 < baseStart_5175787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175813 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 5, 5]
def baseStart_5175813 : Nat := 118140960795 + 5175813 * 2 ^ 59
def prefixEnd_5175813 : Nat := 4983230072969 + 3 ^ 40 * 5175813 * 2
def baseEnd_5175813 : Nat := 885893282263154447178125

theorem tailTrace_5175813 : CollatzResearch.WordTrace tailWord_5175813 prefixEnd_5175813 885893282263154447178125 := by
  unfold tailWord_5175813
  simp only [CollatzResearch.WordTrace]
  refine ⟨188777408797920934329980093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125851605865280622886653395 188777408797920934329980093)
  ·
    refine ⟨70791528299220350373742535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188777408797920934329980093 70791528299220350373742535)
    ·
      refine ⟨106187292448830525560613803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70791528299220350373742535 106187292448830525560613803)
      ·
        refine ⟨159280938673245788340920705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106187292448830525560613803 159280938673245788340920705)
        ·
          refine ⟨119460704004934341255690529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159280938673245788340920705 119460704004934341255690529)
          ·
            refine ⟨89595528003700755941767897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119460704004934341255690529 89595528003700755941767897)
            ·
              refine ⟨67196646002775566956325923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89595528003700755941767897 67196646002775566956325923)
              ·
                refine ⟨100794969004163350434488885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67196646002775566956325923 100794969004163350434488885)
                ·
                  refine ⟨9449528344140314103233333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100794969004163350434488885 9449528344140314103233333)
                  ·
                    refine ⟨885893282263154447178125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9449528344140314103233333 885893282263154447178125)
                    ·
                      rfl

theorem cell23_5175813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_5175813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175813 prefixEnd_5175813 := by exact prefixLift 5175813
  have htrace : WordTrace (prefixWord ++ tailWord_5175813) baseStart_5175813 baseEnd_5175813 := by
    simpa [prefixWord, tailWord_5175813, baseEnd_5175813] using wordTrace_append hprefix tailTrace_5175813
  have hstable : (prefixWord ++ tailWord_5175813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175813).length < 2 ^ (prefixWord ++ tailWord_5175813).sum := by decide
  have hdescent : baseEnd_5175813 < baseStart_5175813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175837 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 1, 5, 2]
def baseStart_5175837 : Nat := 118140960795 + 5175837 * 2 ^ 59
def prefixEnd_5175837 : Nat := 4983230072969 + 3 ^ 40 * 5175837 * 2
def baseEnd_5175837 : Nat := 2657692170325171247634265

theorem tailTrace_5175837 : CollatzResearch.WordTrace tailWord_5175837 prefixEnd_5175837 2657692170325171247634265 := by
  unfold tailWord_5175837
  simp only [CollatzResearch.WordTrace]
  refine ⟨188778284149833986428853765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125852189433222657619235843 188778284149833986428853765)
  ·
    refine ⟨35395928278093872455410081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188778284149833986428853765 35395928278093872455410081)
    ·
      refine ⟨26546946208570404341557561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35395928278093872455410081 26546946208570404341557561)
      ·
        refine ⟨19910209656427803256168171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26546946208570404341557561 19910209656427803256168171)
        ·
          refine ⟨29865314484641704884252257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19910209656427803256168171 29865314484641704884252257)
          ·
            refine ⟨22398985863481278663189193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29865314484641704884252257 22398985863481278663189193)
            ·
              refine ⟨16799239397610958997391895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22398985863481278663189193 16799239397610958997391895)
              ·
                refine ⟨25198859096416438496087843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16799239397610958997391895 25198859096416438496087843)
                ·
                  refine ⟨37798288644624657744131765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25198859096416438496087843 37798288644624657744131765)
                  ·
                    refine ⟨3543589560433561663512353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37798288644624657744131765 3543589560433561663512353)
                    ·
                      refine ⟨2657692170325171247634265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543589560433561663512353 2657692170325171247634265)
                      ·
                        rfl

theorem cell23_5175837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_5175837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175837 prefixEnd_5175837 := by exact prefixLift 5175837
  have htrace : WordTrace (prefixWord ++ tailWord_5175837) baseStart_5175837 baseEnd_5175837 := by
    simpa [prefixWord, tailWord_5175837, baseEnd_5175837] using wordTrace_append hprefix tailTrace_5175837
  have hstable : (prefixWord ++ tailWord_5175837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175837).length < 2 ^ (prefixWord ++ tailWord_5175837).sum := by decide
  have hdescent : baseEnd_5175837 < baseStart_5175837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175861 : List Nat := [1, 3, 3, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_5175861 : Nat := 118140960795 + 5175861 * 2 ^ 59
def prefixEnd_5175861 : Nat := 4983230072969 + 3 ^ 40 * 5175861 * 2
def baseEnd_5175861 : Nat := 2657704493860879153734155

theorem tailTrace_5175861 : CollatzResearch.WordTrace tailWord_5175861 prefixEnd_5175861 2657704493860879153734155 := by
  unfold tailWord_5175861
  simp only [CollatzResearch.WordTrace]
  refine ⟨188779159501747038527727437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125852773001164692351818291 188779159501747038527727437)
  ·
    refine ⟨70792184813155139447897789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188779159501747038527727437 70792184813155139447897789)
    ·
      refine ⟨26547069304933177292961671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70792184813155139447897789 26547069304933177292961671)
      ·
        refine ⟨39820603957399765939442507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26547069304933177292961671 39820603957399765939442507)
        ·
          refine ⟨59730905936099648909163761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39820603957399765939442507 59730905936099648909163761)
          ·
            refine ⟨44798179452074736681872821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59730905936099648909163761 44798179452074736681872821)
            ·
              refine ⟨4199829323632006563925577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44798179452074736681872821 4199829323632006563925577)
              ·
                refine ⟨3149871992724004922944183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4199829323632006563925577 3149871992724004922944183)
                ·
                  refine ⟨4724807989086007384416275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149871992724004922944183 4724807989086007384416275)
                  ·
                    refine ⟨7087211983629011076624413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4724807989086007384416275 7087211983629011076624413)
                    ·
                      refine ⟨2657704493860879153734155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7087211983629011076624413 2657704493860879153734155)
                      ·
                        rfl

theorem cell23_5175861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_5175861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175861 prefixEnd_5175861 := by exact prefixLift 5175861
  have htrace : WordTrace (prefixWord ++ tailWord_5175861) baseStart_5175861 baseEnd_5175861 := by
    simpa [prefixWord, tailWord_5175861, baseEnd_5175861] using wordTrace_append hprefix tailTrace_5175861
  have hstable : (prefixWord ++ tailWord_5175861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175861).length < 2 ^ (prefixWord ++ tailWord_5175861).sum := by decide
  have hdescent : baseEnd_5175861 < baseStart_5175861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175863 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_5175863 : Nat := 118140960795 + 5175863 * 2 ^ 59
def prefixEnd_5175863 : Nat := 4983230072969 + 3 ^ 40 * 5175863 * 2
def baseEnd_5175863 : Nat := 2657705520822188145909145

theorem tailTrace_5175863 : CollatzResearch.WordTrace tailWord_5175863 prefixEnd_5175863 2657705520822188145909145 := by
  unfold tailWord_5175863
  simp only [CollatzResearch.WordTrace]
  refine ⟨188779232447739792869300243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125852821631826528579533495 188779232447739792869300243)
  ·
    refine ⟨283168848671609689303950365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188779232447739792869300243 283168848671609689303950365)
    ·
      refine ⟨106188318251853633488981387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283168848671609689303950365 106188318251853633488981387)
      ·
        refine ⟨159282477377780450233472081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106188318251853633488981387 159282477377780450233472081)
        ·
          refine ⟨119461858033335337675104061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159282477377780450233472081 119461858033335337675104061)
          ·
            refine ⟨44798196762500751628164023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119461858033335337675104061 44798196762500751628164023)
            ·
              refine ⟨67197295143751127442246035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44798196762500751628164023 67197295143751127442246035)
              ·
                refine ⟨100795942715626691163369053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67197295143751127442246035 100795942715626691163369053)
                ·
                  refine ⟨37798478518360009186263395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100795942715626691163369053 37798478518360009186263395)
                  ·
                    refine ⟨56697717777540013779395093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37798478518360009186263395 56697717777540013779395093)
                    ·
                      refine ⟨2657705520822188145909145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56697717777540013779395093 2657705520822188145909145)
                      ·
                        rfl

theorem cell23_5175863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_5175863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175863 prefixEnd_5175863 := by exact prefixLift 5175863
  have htrace : WordTrace (prefixWord ++ tailWord_5175863) baseStart_5175863 baseEnd_5175863 := by
    simpa [prefixWord, tailWord_5175863, baseEnd_5175863] using wordTrace_append hprefix tailTrace_5175863
  have hstable : (prefixWord ++ tailWord_5175863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175863).length < 2 ^ (prefixWord ++ tailWord_5175863).sum := by decide
  have hdescent : baseEnd_5175863 < baseStart_5175863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175877 : List Nat := [1, 3, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_5175877 : Nat := 118140960795 + 5175877 * 2 ^ 59
def prefixEnd_5175877 : Nat := 4983230072969 + 3 ^ 40 * 5175877 * 2
def baseEnd_5175877 : Nat := 885904236517117030378027

theorem tailTrace_5175877 : CollatzResearch.WordTrace tailWord_5175877 prefixEnd_5175877 885904236517117030378027 := by
  unfold tailWord_5175877
  simp only [CollatzResearch.WordTrace]
  refine ⟨188779743069689073260309885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125853162046459382173539923 188779743069689073260309885)
  ·
    refine ⟨70792403651133402472616207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188779743069689073260309885 70792403651133402472616207)
    ·
      refine ⟨106188605476700103708924311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70792403651133402472616207 106188605476700103708924311)
      ·
        refine ⟨159282908215050155563386467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106188605476700103708924311 159282908215050155563386467)
        ·
          refine ⟨238924362322575233345079701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159282908215050155563386467 238924362322575233345079701)
          ·
            refine ⟨11199579483870714063050611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 238924362322575233345079701 11199579483870714063050611)
            ·
              refine ⟨16799369225806071094575917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11199579483870714063050611 16799369225806071094575917)
              ·
                refine ⟨6299763459677276660465969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16799369225806071094575917 6299763459677276660465969)
                ·
                  refine ⟨4724822594757957495349477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6299763459677276660465969 4724822594757957495349477)
                  ·
                    refine ⟨885904236517117030378027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724822594757957495349477 885904236517117030378027)
                    ·
                      rfl

theorem cell23_5175877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_5175877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175877 prefixEnd_5175877 := by exact prefixLift 5175877
  have htrace : WordTrace (prefixWord ++ tailWord_5175877) baseStart_5175877 baseEnd_5175877 := by
    simpa [prefixWord, tailWord_5175877, baseEnd_5175877] using wordTrace_append hprefix tailTrace_5175877
  have hstable : (prefixWord ++ tailWord_5175877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175877).length < 2 ^ (prefixWord ++ tailWord_5175877).sum := by decide
  have hdescent : baseEnd_5175877 < baseStart_5175877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175887 : List Nat := [1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 3]
def baseStart_5175887 : Nat := 118140960795 + 5175887 * 2 ^ 59
def prefixEnd_5175887 : Nat := 4983230072969 + 3 ^ 40 * 5175887 * 2
def baseEnd_5175887 : Nat := 2657717844357896052009035

theorem tailTrace_5175887 : CollatzResearch.WordTrace tailWord_5175887 prefixEnd_5175887 2657717844357896052009035 := by
  unfold tailWord_5175887
  simp only [CollatzResearch.WordTrace]
  refine ⟨188780107799652844968173915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125853405199768563312115943 188780107799652844968173915)
  ·
    refine ⟨283170161699479267452260873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188780107799652844968173915 283170161699479267452260873)
    ·
      refine ⟨212377621274609450589195655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283170161699479267452260873 212377621274609450589195655)
      ·
        refine ⟨318566431911914175883793483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212377621274609450589195655 318566431911914175883793483)
        ·
          refine ⟨477849647867871263825690225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318566431911914175883793483 477849647867871263825690225)
          ·
            refine ⟨358387235900903447869267669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477849647867871263825690225 358387235900903447869267669)
            ·
              refine ⟨8399700841427424559435961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 358387235900903447869267669 8399700841427424559435961)
              ·
                refine ⟨6299775631070568419576971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8399700841427424559435961 6299775631070568419576971)
                ·
                  refine ⟨9449663446605852629365457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6299775631070568419576971 9449663446605852629365457)
                  ·
                    refine ⟨7087247584954389472024093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9449663446605852629365457 7087247584954389472024093)
                    ·
                      refine ⟨2657717844357896052009035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7087247584954389472024093 2657717844357896052009035)
                      ·
                        rfl

theorem cell23_5175887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 3].length) (baseStart_5175887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175887 prefixEnd_5175887 := by exact prefixLift 5175887
  have htrace : WordTrace (prefixWord ++ tailWord_5175887) baseStart_5175887 baseEnd_5175887 := by
    simpa [prefixWord, tailWord_5175887, baseEnd_5175887] using wordTrace_append hprefix tailTrace_5175887
  have hstable : (prefixWord ++ tailWord_5175887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175887).length < 2 ^ (prefixWord ++ tailWord_5175887).sum := by decide
  have hdescent : baseEnd_5175887 < baseStart_5175887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175903 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 4, 7]
def baseStart_5175903 : Nat := 118140960795 + 5175903 * 2 ^ 59
def prefixEnd_5175903 : Nat := 4983230072969 + 3 ^ 40 * 5175903 * 2
def baseEnd_5175903 : Nat := 885908686682789329802987

theorem tailTrace_5175903 : CollatzResearch.WordTrace tailWord_5175903 prefixEnd_5175903 885908686682789329802987 := by
  unfold tailWord_5175903
  simp only [CollatzResearch.WordTrace]
  refine ⟨188780691367594879700756363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125853794245063253133837575 188780691367594879700756363)
  ·
    refine ⟨283171037051392319551134545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188780691367594879700756363 283171037051392319551134545)
    ·
      refine ⟨212378277788544239663350909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283171037051392319551134545 212378277788544239663350909)
      ·
        refine ⟨79641854170704089873756591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212378277788544239663350909 79641854170704089873756591)
        ·
          refine ⟨119462781256056134810634887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79641854170704089873756591 119462781256056134810634887)
          ·
            refine ⟨179194171884084202215952331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119462781256056134810634887 179194171884084202215952331)
            ·
              refine ⟨268791257826126303323928497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179194171884084202215952331 268791257826126303323928497)
              ·
                refine ⟨201593443369594727492946373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268791257826126303323928497 201593443369594727492946373)
                ·
                  refine ⟨37798770631799011404927445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201593443369594727492946373 37798770631799011404927445)
                  ·
                    refine ⟨885908686682789329802987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37798770631799011404927445 885908686682789329802987)
                    ·
                      rfl

theorem cell23_5175903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_5175903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175903 prefixEnd_5175903 := by exact prefixLift 5175903
  have htrace : WordTrace (prefixWord ++ tailWord_5175903) baseStart_5175903 baseEnd_5175903 := by
    simpa [prefixWord, tailWord_5175903, baseEnd_5175903] using wordTrace_append hprefix tailTrace_5175903
  have hstable : (prefixWord ++ tailWord_5175903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175903).length < 2 ^ (prefixWord ++ tailWord_5175903).sum := by decide
  have hdescent : baseEnd_5175903 < baseStart_5175903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175918 : List Nat := [4, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_5175918 : Nat := 118140960795 + 5175918 * 2 ^ 59
def prefixEnd_5175918 : Nat := 4983230072969 + 3 ^ 40 * 5175918 * 2
def baseEnd_5175918 : Nat := 2657733762258185430721393

theorem tailTrace_5175918 : CollatzResearch.WordTrace tailWord_5175918 prefixEnd_5175918 2657733762258185430721393 := by
  unfold tailWord_5175918
  simp only [CollatzResearch.WordTrace]
  refine ⟨23597654807817567157819051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125854158975027024841701605 23597654807817567157819051)
  ·
    refine ⟨35396482211726350736728577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23597654807817567157819051 35396482211726350736728577)
    ·
      refine ⟨26547361658794763052546433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35396482211726350736728577 26547361658794763052546433)
      ·
        refine ⟨19910521244096072289409825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26547361658794763052546433 19910521244096072289409825)
        ·
          refine ⟨14932890933072054217057369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19910521244096072289409825 14932890933072054217057369)
          ·
            refine ⟨11199668199804040662793027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14932890933072054217057369 11199668199804040662793027)
            ·
              refine ⟨16799502299706060994189541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11199668199804040662793027 16799502299706060994189541)
              ·
                refine ⟨3149906681194886436410539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16799502299706060994189541 3149906681194886436410539)
                ·
                  refine ⟨4724860021792329654615809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3149906681194886436410539 4724860021792329654615809)
                  ·
                    refine ⟨3543645016344247240961857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4724860021792329654615809 3543645016344247240961857)
                    ·
                      refine ⟨2657733762258185430721393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543645016344247240961857 2657733762258185430721393)
                      ·
                        rfl

theorem cell23_5175918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_5175918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175918 prefixEnd_5175918 := by exact prefixLift 5175918
  have htrace : WordTrace (prefixWord ++ tailWord_5175918) baseStart_5175918 baseEnd_5175918 := by
    simpa [prefixWord, tailWord_5175918, baseEnd_5175918] using wordTrace_append hprefix tailTrace_5175918
  have hstable : (prefixWord ++ tailWord_5175918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175918).length < 2 ^ (prefixWord ++ tailWord_5175918).sum := by decide
  have hdescent : baseEnd_5175918 < baseStart_5175918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175927 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 3, 3, 2]
def baseStart_5175927 : Nat := 118140960795 + 5175927 * 2 ^ 59
def prefixEnd_5175927 : Nat := 4983230072969 + 3 ^ 40 * 5175927 * 2
def baseEnd_5175927 : Nat := 2657738383584075895508851

theorem tailTrace_5175927 : CollatzResearch.WordTrace tailWord_5175927 prefixEnd_5175927 2657738383584075895508851 := by
  unfold tailWord_5175927
  simp only [CollatzResearch.WordTrace]
  refine ⟨188781566719507931799630035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125854377813005287866420023 188781566719507931799630035)
  ·
    refine ⟨283172350079261897699445053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188781566719507931799630035 283172350079261897699445053)
    ·
      refine ⟨106189631279723211637291895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283172350079261897699445053 106189631279723211637291895)
      ·
        refine ⟨159284446919584817455937843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106189631279723211637291895 159284446919584817455937843)
        ·
          refine ⟨238926670379377226183906765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159284446919584817455937843 238926670379377226183906765)
          ·
            refine ⟨89597501392266459818965037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238926670379377226183906765 89597501392266459818965037)
            ·
              refine ⟨33599063022099922432111889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89597501392266459818965037 33599063022099922432111889)
              ·
                refine ⟨25199297266574941824083917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33599063022099922432111889 25199297266574941824083917)
                ·
                  refine ⟨9449736474965603184031469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25199297266574941824083917 9449736474965603184031469)
                  ·
                    refine ⟨3543651178112101194011801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9449736474965603184031469 3543651178112101194011801)
                    ·
                      refine ⟨2657738383584075895508851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543651178112101194011801 2657738383584075895508851)
                      ·
                        rfl

theorem cell23_5175927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_5175927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175927 prefixEnd_5175927 := by exact prefixLift 5175927
  have htrace : WordTrace (prefixWord ++ tailWord_5175927) baseStart_5175927 baseEnd_5175927 := by
    simpa [prefixWord, tailWord_5175927, baseEnd_5175927] using wordTrace_append hprefix tailTrace_5175927
  have hstable : (prefixWord ++ tailWord_5175927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175927).length < 2 ^ (prefixWord ++ tailWord_5175927).sum := by decide
  have hdescent : baseEnd_5175927 < baseStart_5175927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175950 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_5175950 : Nat := 118140960795 + 5175950 * 2 ^ 59
def prefixEnd_5175950 : Nat := 4983230072969 + 3 ^ 40 * 5175950 * 2
def baseEnd_5175950 : Nat := 885916731213043101840415

theorem tailTrace_5175950 : CollatzResearch.WordTrace tailWord_5175950 prefixEnd_5175950 885916731213043101840415 := by
  unfold tailWord_5175950
  simp only [CollatzResearch.WordTrace]
  refine ⟨23597800699803075840964663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125854937065616404485144869 23597800699803075840964663)
  ·
    refine ⟨35396701049704613761446995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23597800699803075840964663 35396701049704613761446995)
    ·
      refine ⟨53095051574556920642170493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35396701049704613761446995 53095051574556920642170493)
      ·
        refine ⟨19910644340458845240813935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53095051574556920642170493 19910644340458845240813935)
        ·
          refine ⟨29865966510688267861220903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19910644340458845240813935 29865966510688267861220903)
          ·
            refine ⟨44798949766032401791831355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29865966510688267861220903 44798949766032401791831355)
            ·
              refine ⟨67198424649048602687747033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44798949766032401791831355 67198424649048602687747033)
              ·
                refine ⟨50398818486786452015810275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67198424649048602687747033 50398818486786452015810275)
                ·
                  refine ⟨75598227730179678023715413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50398818486786452015810275 75598227730179678023715413)
                  ·
                    refine ⟨885916731213043101840415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75598227730179678023715413 885916731213043101840415)
                    ·
                      rfl

theorem cell23_5175950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_5175950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175950 prefixEnd_5175950 := by exact prefixLift 5175950
  have htrace : WordTrace (prefixWord ++ tailWord_5175950) baseStart_5175950 baseEnd_5175950 := by
    simpa [prefixWord, tailWord_5175950, baseEnd_5175950] using wordTrace_append hprefix tailTrace_5175950
  have hstable : (prefixWord ++ tailWord_5175950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175950).length < 2 ^ (prefixWord ++ tailWord_5175950).sum := by decide
  have hdescent : baseEnd_5175950 < baseStart_5175950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175960 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5175960 : Nat := 118140960795 + 5175960 * 2 ^ 59
def prefixEnd_5175960 : Nat := 4983230072969 + 3 ^ 40 * 5175960 * 2
def baseEnd_5175960 : Nat := 2657755328445674266396199

theorem tailTrace_5175960 : CollatzResearch.WordTrace tailWord_5175960 prefixEnd_5175960 2657755328445674266396199 := by
  unfold tailWord_5175960
  simp only [CollatzResearch.WordTrace]
  refine ⟨94391385164194189217790667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125855180218925585623720889 94391385164194189217790667)
  ·
    refine ⟨141587077746291283826686001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94391385164194189217790667 141587077746291283826686001)
    ·
      refine ⟨106190308309718462870014501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141587077746291283826686001 106190308309718462870014501)
      ·
        refine ⟨19910682808072211788127719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106190308309718462870014501 19910682808072211788127719)
        ·
          refine ⟨29866024212108317682191579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19910682808072211788127719 29866024212108317682191579)
          ·
            refine ⟨44799036318162476523287369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29866024212108317682191579 44799036318162476523287369)
            ·
              refine ⟨33599277238621857392465527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44799036318162476523287369 33599277238621857392465527)
              ·
                refine ⟨50398915857932786088698291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33599277238621857392465527 50398915857932786088698291)
                ·
                  refine ⟨75598373786899179133047437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50398915857932786088698291 75598373786899179133047437)
                  ·
                    refine ⟨28349390170087192174892789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75598373786899179133047437 28349390170087192174892789)
                    ·
                      refine ⟨2657755328445674266396199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28349390170087192174892789 2657755328445674266396199)
                      ·
                        rfl

theorem cell23_5175960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5175960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175960 prefixEnd_5175960 := by exact prefixLift 5175960
  have htrace : WordTrace (prefixWord ++ tailWord_5175960) baseStart_5175960 baseEnd_5175960 := by
    simpa [prefixWord, tailWord_5175960, baseEnd_5175960] using wordTrace_append hprefix tailTrace_5175960
  have hstable : (prefixWord ++ tailWord_5175960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175960).length < 2 ^ (prefixWord ++ tailWord_5175960).sum := by decide
  have hdescent : baseEnd_5175960 < baseStart_5175960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175968 : List Nat := [2, 1, 1, 4, 5, 1, 1, 2, 2, 1, 3]
def baseStart_5175968 : Nat := 118140960795 + 5175968 * 2 ^ 59
def prefixEnd_5175968 : Nat := 4983230072969 + 3 ^ 40 * 5175968 * 2
def baseEnd_5175968 : Nat := 2657759436290910235096163

theorem tailTrace_5175968 : CollatzResearch.WordTrace tailWord_5175968 prefixEnd_5175968 2657759436290910235096163 := by
  unfold tailWord_5175968
  simp only [CollatzResearch.WordTrace]
  refine ⟨94391531056179697900936279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125855374741572930534581705 94391531056179697900936279)
  ·
    refine ⟨141587296584269546851404419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94391531056179697900936279 141587296584269546851404419)
    ·
      refine ⟨212380944876404320277106629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141587296584269546851404419 212380944876404320277106629)
      ·
        refine ⟨39821427164325810051957493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212380944876404320277106629 39821427164325810051957493)
        ·
          refine ⟨3733258796655544692371015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39821427164325810051957493 3733258796655544692371015)
          ·
            refine ⟨5599888194983317038556523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733258796655544692371015 5599888194983317038556523)
            ·
              refine ⟨8399832292474975557834785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5599888194983317038556523 8399832292474975557834785)
              ·
                refine ⟨6299874219356231668376089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8399832292474975557834785 6299874219356231668376089)
                ·
                  refine ⟨4724905664517173751282067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6299874219356231668376089 4724905664517173751282067)
                  ·
                    refine ⟨7087358496775760626923101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4724905664517173751282067 7087358496775760626923101)
                    ·
                      refine ⟨2657759436290910235096163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7087358496775760626923101 2657759436290910235096163)
                      ·
                        rfl

theorem cell23_5175968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_5175968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175968 prefixEnd_5175968 := by exact prefixLift 5175968
  have htrace : WordTrace (prefixWord ++ tailWord_5175968) baseStart_5175968 baseEnd_5175968 := by
    simpa [prefixWord, tailWord_5175968, baseEnd_5175968] using wordTrace_append hprefix tailTrace_5175968
  have hstable : (prefixWord ++ tailWord_5175968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175968).length < 2 ^ (prefixWord ++ tailWord_5175968).sum := by decide
  have hdescent : baseEnd_5175968 < baseStart_5175968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5175991 : List Nat := [1, 1, 3, 1, 6, 2, 1, 1, 1, 4, 2]
def baseStart_5175991 : Nat := 118140960795 + 5175991 * 2 ^ 59
def prefixEnd_5175991 : Nat := 4983230072969 + 3 ^ 40 * 5175991 * 2
def baseEnd_5175991 : Nat := 2657771246345963645108557

theorem tailTrace_5175991 : CollatzResearch.WordTrace tailWord_5175991 prefixEnd_5175991 2657771246345963645108557 := by
  unfold tailWord_5175991
  simp only [CollatzResearch.WordTrace]
  refine ⟨188783900991276070729959827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125855933994184047153306551 188783900991276070729959827)
  ·
    refine ⟨283175851486914106094939741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188783900991276070729959827 283175851486914106094939741)
    ·
      refine ⟨106190944307592789785602403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283175851486914106094939741 106190944307592789785602403)
      ·
        refine ⟨159286416461389184678403605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106190944307592789785602403 159286416461389184678403605)
        ·
          refine ⟨7466550771627618031800169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 159286416461389184678403605 7466550771627618031800169)
          ·
            refine ⟨5599913078720713523850127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7466550771627618031800169 5599913078720713523850127)
            ·
              refine ⟨8399869618081070285775191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5599913078720713523850127 8399869618081070285775191)
              ·
                refine ⟨12599804427121605428662787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8399869618081070285775191 12599804427121605428662787)
                ·
                  refine ⟨18899706640682408142994181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12599804427121605428662787 18899706640682408142994181)
                  ·
                    refine ⟨3543694995127951526811409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18899706640682408142994181 3543694995127951526811409)
                    ·
                      refine ⟨2657771246345963645108557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543694995127951526811409 2657771246345963645108557)
                      ·
                        rfl

theorem cell23_5175991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_5175991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5175991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5175991 prefixEnd_5175991 := by exact prefixLift 5175991
  have htrace : WordTrace (prefixWord ++ tailWord_5175991) baseStart_5175991 baseEnd_5175991 := by
    simpa [prefixWord, tailWord_5175991, baseEnd_5175991] using wordTrace_append hprefix tailTrace_5175991
  have hstable : (prefixWord ++ tailWord_5175991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5175991).length < 2 ^ (prefixWord ++ tailWord_5175991).sum := by decide
  have hdescent : baseEnd_5175991 < baseStart_5175991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5175991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176014 : List Nat := [4, 1, 1, 1, 3, 2, 3, 3, 5]
def baseStart_5176014 : Nat := 118140960795 + 5176014 * 2 ^ 59
def prefixEnd_5176014 : Nat := 4983230072969 + 3 ^ 40 * 5176014 * 2
def baseEnd_5176014 : Nat := 295309228489001895013439

theorem tailTrace_5176014 : CollatzResearch.WordTrace tailWord_5176014 prefixEnd_5176014 295309228489001895013439 := by
  unfold tailWord_5176014
  simp only [CollatzResearch.WordTrace]
  refine ⟨23598092483774093207255887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125856493246795163772031397 23598092483774093207255887)
  ·
    refine ⟨35397138725661139810883831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23598092483774093207255887 35397138725661139810883831)
    ·
      refine ⟨53095708088491709716325747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35397138725661139810883831 53095708088491709716325747)
      ·
        refine ⟨79643562132737564574488621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53095708088491709716325747 79643562132737564574488621)
        ·
          refine ⟨29866335799776586715433233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79643562132737564574488621 29866335799776586715433233)
          ·
            refine ⟨22399751849832440036574925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29866335799776586715433233 22399751849832440036574925)
            ·
              refine ⟨8399906943687165013715597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22399751849832440036574925 8399906943687165013715597)
              ·
                refine ⟨3149965103882686880143349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8399906943687165013715597 3149965103882686880143349)
                ·
                  refine ⟨295309228489001895013439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3149965103882686880143349 295309228489001895013439)
                  ·
                    rfl

theorem cell23_5176014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_5176014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176014 prefixEnd_5176014 := by exact prefixLift 5176014
  have htrace : WordTrace (prefixWord ++ tailWord_5176014) baseStart_5176014 baseEnd_5176014 := by
    simpa [prefixWord, tailWord_5176014, baseEnd_5176014] using wordTrace_append hprefix tailTrace_5176014
  have hstable : (prefixWord ++ tailWord_5176014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176014).length < 2 ^ (prefixWord ++ tailWord_5176014).sum := by decide
  have hdescent : baseEnd_5176014 < baseStart_5176014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176037 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_5176037 : Nat := 118140960795 + 5176037 * 2 ^ 59
def prefixEnd_5176037 : Nat := 4983230072969 + 3 ^ 40 * 5176037 * 2
def baseEnd_5176037 : Nat := 2657794866456070465133345

theorem tailTrace_5176037 : CollatzResearch.WordTrace tailWord_5176037 prefixEnd_5176037 2657794866456070465133345 := by
  unfold tailWord_5176037
  simp only [CollatzResearch.WordTrace]
  refine ⟨188785578749109420586134365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125857052499406280390756243 188785578749109420586134365)
  ·
    refine ⟨70794592030916032719800387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188785578749109420586134365 70794592030916032719800387)
    ·
      refine ⟨106191888046374049079700581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70794592030916032719800387 106191888046374049079700581)
      ·
        refine ⟨19910979008695134202443859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106191888046374049079700581 19910979008695134202443859)
        ·
          refine ⟨29866468513042701303665789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19910979008695134202443859 29866468513042701303665789)
          ·
            refine ⟨11199925692391012988874671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29866468513042701303665789 11199925692391012988874671)
            ·
              refine ⟨16799888538586519483312007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11199925692391012988874671 16799888538586519483312007)
              ·
                refine ⟨25199832807879779224968011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16799888538586519483312007 25199832807879779224968011)
                ·
                  refine ⟨37799749211819668837452017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25199832807879779224968011 37799749211819668837452017)
                  ·
                    refine ⟨28349811908864751628089013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37799749211819668837452017 28349811908864751628089013)
                    ·
                      refine ⟨2657794866456070465133345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28349811908864751628089013 2657794866456070465133345)
                      ·
                        rfl

theorem cell23_5176037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_5176037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176037 prefixEnd_5176037 := by exact prefixLift 5176037
  have htrace : WordTrace (prefixWord ++ tailWord_5176037) baseStart_5176037 baseEnd_5176037 := by
    simpa [prefixWord, tailWord_5176037, baseEnd_5176037] using wordTrace_append hprefix tailTrace_5176037
  have hstable : (prefixWord ++ tailWord_5176037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176037).length < 2 ^ (prefixWord ++ tailWord_5176037).sum := by decide
  have hdescent : baseEnd_5176037 < baseStart_5176037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176057 : List Nat := [1, 2, 1, 3, 1, 1, 1, 6, 3, 4]
def baseStart_5176057 : Nat := 118140960795 + 5176057 * 2 ^ 59
def prefixEnd_5176057 : Nat := 4983230072969 + 3 ^ 40 * 5176057 * 2
def baseEnd_5176057 : Nat := 885935045356386795627751

theorem tailTrace_5176057 : CollatzResearch.WordTrace tailWord_5176057 prefixEnd_5176057 885935045356386795627751 := by
  unfold tailWord_5176057
  simp only [CollatzResearch.WordTrace]
  refine ⟨188786308209036964001862425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125857538806024642667908283 188786308209036964001862425)
  ·
    refine ⟨141589731156777723001396819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188786308209036964001862425 141589731156777723001396819)
    ·
      refine ⟨212384596735166584502095229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141589731156777723001396819 212384596735166584502095229)
      ·
        refine ⟨79644223775687469188285711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212384596735166584502095229 79644223775687469188285711)
        ·
          refine ⟨119466335663531203782428567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79644223775687469188285711 119466335663531203782428567)
          ·
            refine ⟨179199503495296805673642851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119466335663531203782428567 179199503495296805673642851)
            ·
              refine ⟨268799255242945208510464277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179199503495296805673642851 268799255242945208510464277)
              ·
                refine ⟨12599965089513056648928013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 268799255242945208510464277 12599965089513056648928013)
                ·
                  refine ⟨4724986908567396243348005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12599965089513056648928013 4724986908567396243348005)
                  ·
                    refine ⟨885935045356386795627751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4724986908567396243348005 885935045356386795627751)
                    ·
                      rfl

theorem cell23_5176057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 4].length) (baseStart_5176057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176057 prefixEnd_5176057 := by exact prefixLift 5176057
  have htrace : WordTrace (prefixWord ++ tailWord_5176057) baseStart_5176057 baseEnd_5176057 := by
    simpa [prefixWord, tailWord_5176057, baseEnd_5176057] using wordTrace_append hprefix tailTrace_5176057
  have hstable : (prefixWord ++ tailWord_5176057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176057).length < 2 ^ (prefixWord ++ tailWord_5176057).sum := by decide
  have hdescent : baseEnd_5176057 < baseStart_5176057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176148 : List Nat := [2, 4, 1, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_5176148 : Nat := 118140960795 + 5176148 * 2 ^ 59
def prefixEnd_5176148 : Nat := 4983230072969 + 3 ^ 40 * 5176148 * 2
def baseEnd_5176148 : Nat := 2657851862808719530845335

theorem tailTrace_5176148 : CollatzResearch.WordTrace tailWord_5176148 prefixEnd_5176148 2657851862808719530845335 := by
  unfold tailWord_5176148
  simp only [CollatzResearch.WordTrace]
  refine ⟨94394813625853643271712549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125859751501138191028950065 94394813625853643271712549)
  ·
    refine ⟨17699027554847558113446103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94394813625853643271712549 17699027554847558113446103)
    ·
      refine ⟨26548541332271337170169155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17699027554847558113446103 26548541332271337170169155)
      ·
        refine ⟨39822811998407005755253733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26548541332271337170169155 39822811998407005755253733)
        ·
          refine ⟨7466777249701313579110075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39822811998407005755253733 7466777249701313579110075)
          ·
            refine ⟨11200165874551970368665113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7466777249701313579110075 11200165874551970368665113)
            ·
              refine ⟨8400124405913977776498835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11200165874551970368665113 8400124405913977776498835)
              ·
                refine ⟨12600186608870966664748253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8400124405913977776498835 12600186608870966664748253)
                ·
                  refine ⟨4725069978326612499280595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12600186608870966664748253 4725069978326612499280595)
                  ·
                    refine ⟨7087604967489918748920893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4725069978326612499280595 7087604967489918748920893)
                    ·
                      refine ⟨2657851862808719530845335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7087604967489918748920893 2657851862808719530845335)
                      ·
                        rfl

theorem cell23_5176148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_5176148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176148 prefixEnd_5176148 := by exact prefixLift 5176148
  have htrace : WordTrace (prefixWord ++ tailWord_5176148) baseStart_5176148 baseEnd_5176148 := by
    simpa [prefixWord, tailWord_5176148, baseEnd_5176148] using wordTrace_append hprefix tailTrace_5176148
  have hstable : (prefixWord ++ tailWord_5176148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176148).length < 2 ^ (prefixWord ++ tailWord_5176148).sum := by decide
  have hdescent : baseEnd_5176148 < baseStart_5176148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176164 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 1, 6]
def baseStart_5176164 : Nat := 118140960795 + 5176164 * 2 ^ 59
def prefixEnd_5176164 : Nat := 4983230072969 + 3 ^ 40 * 5176164 * 2
def baseEnd_5176164 : Nat := 885953359499730489415087

theorem tailTrace_5176164 : CollatzResearch.WordTrace tailWord_5176164 prefixEnd_5176164 885953359499730489415087 := by
  unfold tailWord_5176164
  simp only [CollatzResearch.WordTrace]
  refine ⟨94395105409824660638003773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125860140546432880850671697 94395105409824660638003773)
  ·
    refine ⟨35398164528684247739251415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94395105409824660638003773 35398164528684247739251415)
    ·
      refine ⟨53097246793026371608877123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35398164528684247739251415 53097246793026371608877123)
      ·
        refine ⟨79645870189539557413315685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53097246793026371608877123 79645870189539557413315685)
        ·
          refine ⟨14933600660538667014996691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79645870189539557413315685 14933600660538667014996691)
          ·
            refine ⟨22400400990808000522495037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14933600660538667014996691 22400400990808000522495037)
            ·
              refine ⟨8400150371553000195935639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22400400990808000522495037 8400150371553000195935639)
              ·
                refine ⟨12600225557329500293903459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8400150371553000195935639 12600225557329500293903459)
                ·
                  refine ⟨18900338335994250440855189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12600225557329500293903459 18900338335994250440855189)
                  ·
                    refine ⟨885953359499730489415087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18900338335994250440855189 885953359499730489415087)
                    ·
                      rfl

theorem cell23_5176164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_5176164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176164 prefixEnd_5176164 := by exact prefixLift 5176164
  have htrace : WordTrace (prefixWord ++ tailWord_5176164) baseStart_5176164 baseEnd_5176164 := by
    simpa [prefixWord, tailWord_5176164, baseEnd_5176164] using wordTrace_append hprefix tailTrace_5176164
  have hstable : (prefixWord ++ tailWord_5176164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176164).length < 2 ^ (prefixWord ++ tailWord_5176164).sum := by decide
  have hdescent : baseEnd_5176164 < baseStart_5176164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176171 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 3, 2, 2]
def baseStart_5176171 : Nat := 118140960795 + 5176171 * 2 ^ 59
def prefixEnd_5176171 : Nat := 4983230072969 + 3 ^ 40 * 5176171 * 2
def baseEnd_5176171 : Nat := 2657863672863772940857729

theorem tailTrace_5176171 : CollatzResearch.WordTrace tailWord_5176171 prefixEnd_5176171 2657863672863772940857729 := by
  unfold tailWord_5176171
  simp only [CollatzResearch.WordTrace]
  refine ⟨188790466130623961471512367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125860310753749307647674911 188790466130623961471512367)
  ·
    refine ⟨283185699195935942207268551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188790466130623961471512367 283185699195935942207268551)
    ·
      refine ⟨424778548793903913310902827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283185699195935942207268551 424778548793903913310902827)
      ·
        refine ⟨637167823190855869966354241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424778548793903913310902827 637167823190855869966354241)
        ·
          refine ⟨477875867393141902474765681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637167823190855869966354241 477875867393141902474765681)
          ·
            refine ⟨358406900544856426856074261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477875867393141902474765681 358406900544856426856074261)
            ·
              refine ⟨16800323463040145008878481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 358406900544856426856074261 16800323463040145008878481)
              ·
                refine ⟨12600242597280108756658861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16800323463040145008878481 12600242597280108756658861)
                ·
                  refine ⟨4725090973980040783747073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12600242597280108756658861 4725090973980040783747073)
                  ·
                    refine ⟨3543818230485030587810305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4725090973980040783747073 3543818230485030587810305)
                    ·
                      refine ⟨2657863672863772940857729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543818230485030587810305 2657863672863772940857729)
                      ·
                        rfl

theorem cell23_5176171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 2, 2].length) (baseStart_5176171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176171 prefixEnd_5176171 := by exact prefixLift 5176171
  have htrace : WordTrace (prefixWord ++ tailWord_5176171) baseStart_5176171 baseEnd_5176171 := by
    simpa [prefixWord, tailWord_5176171, baseEnd_5176171] using wordTrace_append hprefix tailTrace_5176171
  have hstable : (prefixWord ++ tailWord_5176171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176171).length < 2 ^ (prefixWord ++ tailWord_5176171).sum := by decide
  have hdescent : baseEnd_5176171 < baseStart_5176171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176177 : List Nat := [1, 2, 2, 2, 1, 5, 1, 9]
def baseStart_5176177 : Nat := 118140960795 + 5176177 * 2 ^ 59
def prefixEnd_5176177 : Nat := 4983230072969 + 3 ^ 40 * 5176177 * 2
def baseEnd_5176177 : Nat := 98439509398062959903063

theorem tailTrace_5176177 : CollatzResearch.WordTrace tailWord_5176177 prefixEnd_5176177 98439509398062959903063 := by
  unfold tailWord_5176177
  simp only [CollatzResearch.WordTrace]
  refine ⟨188790684968602224496230785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125860456645734816330820523 188790684968602224496230785)
  ·
    refine ⟨141593013726451668372173089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188790684968602224496230785 141593013726451668372173089)
    ·
      refine ⟨106194760294838751279129817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141593013726451668372173089 106194760294838751279129817)
      ·
        refine ⟨79646070221129063459347363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106194760294838751279129817 79646070221129063459347363)
        ·
          refine ⟨119469105331693595189021045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79646070221129063459347363 119469105331693595189021045)
          ·
            refine ⟨11200228624846274548970723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119469105331693595189021045 11200228624846274548970723)
            ·
              refine ⟨16800342937269411823456085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11200228624846274548970723 16800342937269411823456085)
              ·
                refine ⟨98439509398062959903063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16800342937269411823456085 98439509398062959903063)
                ·
                  rfl

theorem cell23_5176177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 9].length) (baseStart_5176177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176177 prefixEnd_5176177 := by exact prefixLift 5176177
  have htrace : WordTrace (prefixWord ++ tailWord_5176177) baseStart_5176177 baseEnd_5176177 := by
    simpa [prefixWord, tailWord_5176177, baseEnd_5176177] using wordTrace_append hprefix tailTrace_5176177
  have hstable : (prefixWord ++ tailWord_5176177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176177).length < 2 ^ (prefixWord ++ tailWord_5176177).sum := by decide
  have hdescent : baseEnd_5176177 < baseStart_5176177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176182 : List Nat := [5, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5176182 : Nat := 118140960795 + 5176182 * 2 ^ 59
def prefixEnd_5176182 : Nat := 4983230072969 + 3 ^ 40 * 5176182 * 2
def baseEnd_5176182 : Nat := 2657869321150972397820179

theorem tailTrace_5176182 : CollatzResearch.WordTrace tailWord_5176182 prefixEnd_5176182 2657869321150972397820179 := by
  unfold tailWord_5176182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11799429208349006896885175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125860578222389406900108533 11799429208349006896885175)
  ·
    refine ⟨17699143812523510345327763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11799429208349006896885175 17699143812523510345327763)
    ·
      refine ⟨26548715718785265517991645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17699143812523510345327763 26548715718785265517991645)
      ·
        refine ⟨9955768394544474569246867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26548715718785265517991645 9955768394544474569246867)
        ·
          refine ⟨14933652591816711853870301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9955768394544474569246867 14933652591816711853870301)
          ·
            refine ⟨5600119721931266945201363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14933652591816711853870301 5600119721931266945201363)
            ·
              refine ⟨8400179582896900417802045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600119721931266945201363 8400179582896900417802045)
              ·
                refine ⟨3150067343586337656675767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8400179582896900417802045 3150067343586337656675767)
                ·
                  refine ⟨4725101015379506485013651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150067343586337656675767 4725101015379506485013651)
                  ·
                    refine ⟨7087651523069259727520477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4725101015379506485013651 7087651523069259727520477)
                    ·
                      refine ⟨2657869321150972397820179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7087651523069259727520477 2657869321150972397820179)
                      ·
                        rfl

theorem cell23_5176182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5176182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176182 prefixEnd_5176182 := by exact prefixLift 5176182
  have htrace : WordTrace (prefixWord ++ tailWord_5176182) baseStart_5176182 baseEnd_5176182 := by
    simpa [prefixWord, tailWord_5176182, baseEnd_5176182] using wordTrace_append hprefix tailTrace_5176182
  have hstable : (prefixWord ++ tailWord_5176182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176182).length < 2 ^ (prefixWord ++ tailWord_5176182).sum := by decide
  have hdescent : baseEnd_5176182 < baseStart_5176182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176254 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_5176254 : Nat := 118140960795 + 5176254 * 2 ^ 59
def prefixEnd_5176254 : Nat := 4983230072969 + 3 ^ 40 * 5176254 * 2
def baseEnd_5176254 : Nat := 885968763919365372039949

theorem tailTrace_5176254 : CollatzResearch.WordTrace tailWord_5176254 prefixEnd_5176254 885968763919365372039949 := by
  unfold tailWord_5176254
  simp only [CollatzResearch.WordTrace]
  refine ⟨23599186673665408330847977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125862328926215511097855877 23599186673665408330847977)
  ·
    refine ⟨17699390005249056248135983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23599186673665408330847977 17699390005249056248135983)
    ·
      refine ⟨26549085007873584372203975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17699390005249056248135983 26549085007873584372203975)
      ·
        refine ⟨39823627511810376558305963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26549085007873584372203975 39823627511810376558305963)
        ·
          refine ⟨59735441267715564837458945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39823627511810376558305963 59735441267715564837458945)
          ·
            refine ⟨44801580950786673628094209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59735441267715564837458945 44801580950786673628094209)
            ·
              refine ⟨33601185713090005221070657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44801580950786673628094209 33601185713090005221070657)
              ·
                refine ⟨25200889284817503915802993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33601185713090005221070657 25200889284817503915802993)
                ·
                  refine ⟨18900666963613127936852245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25200889284817503915802993 18900666963613127936852245)
                  ·
                    refine ⟨885968763919365372039949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18900666963613127936852245 885968763919365372039949)
                    ·
                      rfl

theorem cell23_5176254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_5176254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176254 prefixEnd_5176254 := by exact prefixLift 5176254
  have htrace : WordTrace (prefixWord ++ tailWord_5176254) baseStart_5176254 baseEnd_5176254 := by
    simpa [prefixWord, tailWord_5176254, baseEnd_5176254] using wordTrace_append hprefix tailTrace_5176254
  have hstable : (prefixWord ++ tailWord_5176254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176254).length < 2 ^ (prefixWord ++ tailWord_5176254).sum := by decide
  have hdescent : baseEnd_5176254 < baseStart_5176254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176261 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 8, 2, 2]
def baseStart_5176261 : Nat := 118140960795 + 5176261 * 2 ^ 59
def prefixEnd_5176261 : Nat := 4983230072969 + 3 ^ 40 * 5176261 * 2
def baseEnd_5176261 : Nat := 2657909886122677588732315

theorem tailTrace_5176261 : CollatzResearch.WordTrace tailWord_5176261 prefixEnd_5176261 2657909886122677588732315 := by
  unfold tailWord_5176261
  simp only [CollatzResearch.WordTrace]
  refine ⟨188793748700297906842288637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125862499133531937894859091 188793748700297906842288637)
  ·
    refine ⟨70797655762611715065858239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188793748700297906842288637 70797655762611715065858239)
    ·
      refine ⟨106196483643917572598787359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70797655762611715065858239 106196483643917572598787359)
      ·
        refine ⟨159294725465876358898181039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106196483643917572598787359 159294725465876358898181039)
        ·
          refine ⟨238942088198814538347271559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159294725465876358898181039 238942088198814538347271559)
          ·
            refine ⟨358413132298221807520907339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238942088198814538347271559 358413132298221807520907339)
            ·
              refine ⟨537619698447332711281361009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358413132298221807520907339 537619698447332711281361009)
              ·
                refine ⟨403214773835499533461020757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537619698447332711281361009 403214773835499533461020757)
                ·
                  refine ⟨4725173130884760157746337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 403214773835499533461020757 4725173130884760157746337)
                  ·
                    refine ⟨3543879848163570118309753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4725173130884760157746337 3543879848163570118309753)
                    ·
                      refine ⟨2657909886122677588732315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543879848163570118309753 2657909886122677588732315)
                      ·
                        rfl

theorem cell23_5176261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 2, 2].length) (baseStart_5176261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176261 prefixEnd_5176261 := by exact prefixLift 5176261
  have htrace : WordTrace (prefixWord ++ tailWord_5176261) baseStart_5176261 baseEnd_5176261 := by
    simpa [prefixWord, tailWord_5176261, baseEnd_5176261] using wordTrace_append hprefix tailTrace_5176261
  have hstable : (prefixWord ++ tailWord_5176261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176261).length < 2 ^ (prefixWord ++ tailWord_5176261).sum := by decide
  have hdescent : baseEnd_5176261 < baseStart_5176261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176262 : List Nat := [6, 1, 3, 1, 1, 2, 1, 8]
def baseStart_5176262 : Nat := 118140960795 + 5176262 * 2 ^ 59
def prefixEnd_5176262 : Nat := 4983230072969 + 3 ^ 40 * 5176262 * 2
def baseEnd_5176262 : Nat := 98441125911234521659993

theorem tailTrace_5176262 : CollatzResearch.WordTrace tailWord_5176262 prefixEnd_5176262 98441125911234521659993 := by
  unfold tailWord_5176262
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899805786665446375408595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 125862523448862856008716693 5899805786665446375408595)
  ·
    refine ⟨8849708679998169563112893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5899805786665446375408595 8849708679998169563112893)
    ·
      refine ⟨3318640754999313586167335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8849708679998169563112893 3318640754999313586167335)
      ·
        refine ⟨4977961132498970379251003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3318640754999313586167335 4977961132498970379251003)
        ·
          refine ⟨7466941698748455568876505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4977961132498970379251003 7466941698748455568876505)
          ·
            refine ⟨5600206274061341676657379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7466941698748455568876505 5600206274061341676657379)
            ·
              refine ⟨8400309411092012514986069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600206274061341676657379 8400309411092012514986069)
              ·
                refine ⟨98441125911234521659993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8400309411092012514986069 98441125911234521659993)
                ·
                  rfl

theorem cell23_5176262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_5176262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176262 prefixEnd_5176262 := by exact prefixLift 5176262
  have htrace : WordTrace (prefixWord ++ tailWord_5176262) baseStart_5176262 baseEnd_5176262 := by
    simpa [prefixWord, tailWord_5176262, baseEnd_5176262] using wordTrace_append hprefix tailTrace_5176262
  have hstable : (prefixWord ++ tailWord_5176262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176262).length < 2 ^ (prefixWord ++ tailWord_5176262).sum := by decide
  have hdescent : baseEnd_5176262 < baseStart_5176262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176314 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_5176314 : Nat := 118140960795 + 5176314 * 2 ^ 59
def prefixEnd_5176314 : Nat := 4983230072969 + 3 ^ 40 * 5176314 * 2
def baseEnd_5176314 : Nat := 885979033532455293789857

theorem tailTrace_5176314 : CollatzResearch.WordTrace tailWord_5176314 prefixEnd_5176314 885979033532455293789857 := by
  unfold tailWord_5176314
  simp only [CollatzResearch.WordTrace]
  refine ⟨47198920442276474223491999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125863787846070597929311997 47198920442276474223491999)
  ·
    refine ⟨70798380663414711335237999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47198920442276474223491999 70798380663414711335237999)
    ·
      refine ⟨106197570995122067002856999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70798380663414711335237999 106197570995122067002856999)
      ·
        refine ⟨159296356492683100504285499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106197570995122067002856999 159296356492683100504285499)
        ·
          refine ⟨238944534739024650756428249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159296356492683100504285499 238944534739024650756428249)
          ·
            refine ⟨179208401054268488067321187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238944534739024650756428249 179208401054268488067321187)
            ·
              refine ⟨268812601581402732100981781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179208401054268488067321187 268812601581402732100981781)
              ·
                refine ⟨12600590699128253067233521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 268812601581402732100981781 12600590699128253067233521)
                ·
                  refine ⟨9450443024346189800425141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12600590699128253067233521 9450443024346189800425141)
                  ·
                    refine ⟨885979033532455293789857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9450443024346189800425141 885979033532455293789857)
                    ·
                      rfl

theorem cell23_5176314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_5176314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176314 prefixEnd_5176314 := by exact prefixLift 5176314
  have htrace : WordTrace (prefixWord ++ tailWord_5176314) baseStart_5176314 baseEnd_5176314 := by
    simpa [prefixWord, tailWord_5176314, baseEnd_5176314] using wordTrace_append hprefix tailTrace_5176314
  have hstable : (prefixWord ++ tailWord_5176314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176314).length < 2 ^ (prefixWord ++ tailWord_5176314).sum := by decide
  have hdescent : baseEnd_5176314 < baseStart_5176314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176318 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_5176318 : Nat := 118140960795 + 5176318 * 2 ^ 59
def prefixEnd_5176318 : Nat := 4983230072969 + 3 ^ 40 * 5176318 * 2
def baseEnd_5176318 : Nat := 295326572724442651746617

theorem tailTrace_5176318 : CollatzResearch.WordTrace tailWord_5176318 prefixEnd_5176318 295326572724442651746617 := by
  unfold tailWord_5176318
  simp only [CollatzResearch.WordTrace]
  refine ⟨23599478457636425697139201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125863885107394270384742405 23599478457636425697139201)
  ·
    refine ⟨17699608843227319272854401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23599478457636425697139201 17699608843227319272854401)
    ·
      refine ⟨13274706632420489454640801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17699608843227319272854401 13274706632420489454640801)
      ·
        refine ⟨9956029974315367090980601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13274706632420489454640801 9956029974315367090980601)
        ·
          refine ⟨7467022480736525318235451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9956029974315367090980601 7467022480736525318235451)
          ·
            refine ⟨11200533721104787977353177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467022480736525318235451 11200533721104787977353177)
            ·
              refine ⟨8400400290828590983014883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11200533721104787977353177 8400400290828590983014883)
              ·
                refine ⟨12600600436242886474522325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8400400290828590983014883 12600600436242886474522325)
                ·
                  refine ⟨295326572724442651746617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12600600436242886474522325 295326572724442651746617)
                  ·
                    rfl

theorem cell23_5176318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_5176318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176318 prefixEnd_5176318 := by exact prefixLift 5176318
  have htrace : WordTrace (prefixWord ++ tailWord_5176318) baseStart_5176318 baseEnd_5176318 := by
    simpa [prefixWord, tailWord_5176318, baseEnd_5176318] using wordTrace_append hprefix tailTrace_5176318
  have hstable : (prefixWord ++ tailWord_5176318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176318).length < 2 ^ (prefixWord ++ tailWord_5176318).sum := by decide
  have hdescent : baseEnd_5176318 < baseStart_5176318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176352 : List Nat := [2, 1, 1, 7, 2, 1, 1, 3, 5]
def baseStart_5176352 : Nat := 118140960795 + 5176352 * 2 ^ 59
def prefixEnd_5176352 : Nat := 4983230072969 + 3 ^ 40 * 5176352 * 2
def baseEnd_5176352 : Nat := 295328512540248525854933

theorem tailTrace_5176352 : CollatzResearch.WordTrace tailWord_5176352 prefixEnd_5176352 295328512540248525854933 := by
  unfold tailWord_5176352
  simp only [CollatzResearch.WordTrace]
  refine ⟨94398533871484114691925655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125864711828645486255900873 94398533871484114691925655)
  ·
    refine ⟨141597800807226172037888483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94398533871484114691925655 141597800807226172037888483)
    ·
      refine ⟨212396701210839258056832725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141597800807226172037888483 212396701210839258056832725)
      ·
        refine ⟨4978047684629045110707017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 212396701210839258056832725 4978047684629045110707017)
        ·
          refine ⟨3733535763471783833030263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4978047684629045110707017 3733535763471783833030263)
          ·
            refine ⟨5600303645207675749545395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733535763471783833030263 5600303645207675749545395)
            ·
              refine ⟨8400455467811513624318093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600303645207675749545395 8400455467811513624318093)
              ·
                refine ⟨3150170800429317609119285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8400455467811513624318093 3150170800429317609119285)
                ·
                  refine ⟨295328512540248525854933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3150170800429317609119285 295328512540248525854933)
                  ·
                    rfl

theorem cell23_5176352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 5].length) (baseStart_5176352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176352 prefixEnd_5176352 := by exact prefixLift 5176352
  have htrace : WordTrace (prefixWord ++ tailWord_5176352) baseStart_5176352 baseEnd_5176352 := by
    simpa [prefixWord, tailWord_5176352, baseEnd_5176352] using wordTrace_append hprefix tailTrace_5176352
  have hstable : (prefixWord ++ tailWord_5176352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176352).length < 2 ^ (prefixWord ++ tailWord_5176352).sum := by decide
  have hdescent : baseEnd_5176352 < baseStart_5176352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176378 : List Nat := [3, 1, 1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_5176378 : Nat := 118140960795 + 5176378 * 2 ^ 59
def prefixEnd_5176378 : Nat := 4983230072969 + 3 ^ 40 * 5176378 * 2
def baseEnd_5176378 : Nat := 885989987786417876989759

theorem tailTrace_5176378 : CollatzResearch.WordTrace tailWord_5176378 prefixEnd_5176378 885989987786417876989759 := by
  unfold tailWord_5176378
  simp only [CollatzResearch.WordTrace]
  refine ⟨47199504010218508956074447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125865344027249357216198525 47199504010218508956074447)
  ·
    refine ⟨70799256015327763434111671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47199504010218508956074447 70799256015327763434111671)
    ·
      refine ⟨106198884022991645151167507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70799256015327763434111671 106198884022991645151167507)
      ·
        refine ⟨159298326034487467726751261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106198884022991645151167507 159298326034487467726751261)
        ·
          refine ⟨59736872262932800397531723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159298326034487467726751261 59736872262932800397531723)
          ·
            refine ⟨89605308394399200596297585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59736872262932800397531723 89605308394399200596297585)
            ·
              refine ⟨67203981295799400447223189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89605308394399200596297585 67203981295799400447223189)
              ·
                refine ⟨3150186623240596895963587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67203981295799400447223189 3150186623240596895963587)
                ·
                  refine ⟨4725279934860895343945381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150186623240596895963587 4725279934860895343945381)
                  ·
                    refine ⟨885989987786417876989759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4725279934860895343945381 885989987786417876989759)
                    ·
                      rfl

theorem cell23_5176378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_5176378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176378 prefixEnd_5176378 := by exact prefixLift 5176378
  have htrace : WordTrace (prefixWord ++ tailWord_5176378) baseStart_5176378 baseEnd_5176378 := by
    simpa [prefixWord, tailWord_5176378, baseEnd_5176378] using wordTrace_append hprefix tailTrace_5176378
  have hstable : (prefixWord ++ tailWord_5176378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176378).length < 2 ^ (prefixWord ++ tailWord_5176378).sum := by decide
  have hdescent : baseEnd_5176378 < baseStart_5176378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176391 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 6]
def baseStart_5176391 : Nat := 118140960795 + 5176391 * 2 ^ 59
def prefixEnd_5176391 : Nat := 4983230072969 + 3 ^ 40 * 5176391 * 2
def baseEnd_5176391 : Nat := 295330737623084675567413

theorem tailTrace_5176391 : CollatzResearch.WordTrace tailWord_5176391 prefixEnd_5176391 295330737623084675567413 := by
  unfold tailWord_5176391
  simp only [CollatzResearch.WordTrace]
  refine ⟨188798490189826939044521027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125865660126551292696347351 188798490189826939044521027)
  ·
    refine ⟨283197735284740408566781541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188798490189826939044521027 283197735284740408566781541)
    ·
      refine ⟨53099575365888826606271539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283197735284740408566781541 53099575365888826606271539)
      ·
        refine ⟨79649363048833239909407309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53099575365888826606271539 79649363048833239909407309)
        ·
          refine ⟨29868511143312464966027741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79649363048833239909407309 29868511143312464966027741)
          ·
            refine ⟨11200691678742174362260403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29868511143312464966027741 11200691678742174362260403)
            ·
              refine ⟨16801037518113261543390605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11200691678742174362260403 16801037518113261543390605)
              ·
                refine ⟨6300389069292473078771477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16801037518113261543390605 6300389069292473078771477)
                ·
                  refine ⟨295330737623084675567413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6300389069292473078771477 295330737623084675567413)
                  ·
                    rfl

theorem cell23_5176391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 6].length) (baseStart_5176391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176391 prefixEnd_5176391 := by exact prefixLift 5176391
  have htrace : WordTrace (prefixWord ++ tailWord_5176391) baseStart_5176391 baseEnd_5176391 := by
    simpa [prefixWord, tailWord_5176391, baseEnd_5176391] using wordTrace_append hprefix tailTrace_5176391
  have hstable : (prefixWord ++ tailWord_5176391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176391).length < 2 ^ (prefixWord ++ tailWord_5176391).sum := by decide
  have hdescent : baseEnd_5176391 < baseStart_5176391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176394 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_5176394 : Nat := 118140960795 + 5176394 * 2 ^ 59
def prefixEnd_5176394 : Nat := 4983230072969 + 3 ^ 40 * 5176394 * 2
def baseEnd_5176394 : Nat := 2657978179049725568369203

theorem tailTrace_5176394 : CollatzResearch.WordTrace tailWord_5176394 prefixEnd_5176394 2657978179049725568369203 := by
  unfold tailWord_5176394
  simp only [CollatzResearch.WordTrace]
  refine ⟨47199649902204017639220059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125865733072544047037920157 47199649902204017639220059)
  ·
    refine ⟨70799474853306026458830089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47199649902204017639220059 70799474853306026458830089)
    ·
      refine ⟨53099606139979519844122567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70799474853306026458830089 53099606139979519844122567)
      ·
        refine ⟨79649409209969279766183851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53099606139979519844122567 79649409209969279766183851)
        ·
          refine ⟨119474113814953919649275777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79649409209969279766183851 119474113814953919649275777)
          ·
            refine ⟨89605585361215439736956833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119474113814953919649275777 89605585361215439736956833)
            ·
              refine ⟨67204189020911579802717625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89605585361215439736956833 67204189020911579802717625)
              ·
                refine ⟨50403141765683684852038219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67204189020911579802717625 50403141765683684852038219)
                ·
                  refine ⟨75604712648525527278057329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50403141765683684852038219 75604712648525527278057329)
                  ·
                    refine ⟨56703534486394145458542997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75604712648525527278057329 56703534486394145458542997)
                    ·
                      refine ⟨2657978179049725568369203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56703534486394145458542997 2657978179049725568369203)
                      ·
                        rfl

theorem cell23_5176394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_5176394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176394 prefixEnd_5176394 := by exact prefixLift 5176394
  have htrace : WordTrace (prefixWord ++ tailWord_5176394) baseStart_5176394 baseEnd_5176394 := by
    simpa [prefixWord, tailWord_5176394, baseEnd_5176394] using wordTrace_append hprefix tailTrace_5176394
  have hstable : (prefixWord ++ tailWord_5176394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176394).length < 2 ^ (prefixWord ++ tailWord_5176394).sum := by decide
  have hdescent : baseEnd_5176394 < baseStart_5176394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176428 : List Nat := [2, 2, 1, 1, 3, 2, 1, 4, 2, 3, 2]
def baseStart_5176428 : Nat := 118140960795 + 5176428 * 2 ^ 59
def prefixEnd_5176428 : Nat := 4983230072969 + 3 ^ 40 * 5176428 * 2
def baseEnd_5176428 : Nat := 2657995637391978435344047

theorem tailTrace_5176428 : CollatzResearch.WordTrace tailWord_5176428 prefixEnd_5176428 2657995637391978435344047 := by
  unfold tailWord_5176428
  simp only [CollatzResearch.WordTrace]
  refine ⟨94399919845346447181808969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125866559793795262909078625 94399919845346447181808969)
  ·
    refine ⟨70799939884009835386356727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94399919845346447181808969 70799939884009835386356727)
    ·
      refine ⟨106199909826014753079535091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70799939884009835386356727 106199909826014753079535091)
      ·
        refine ⟨159299864739022129619302637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106199909826014753079535091 159299864739022129619302637)
        ·
          refine ⟨59737449277133298607238489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159299864739022129619302637 59737449277133298607238489)
          ·
            refine ⟨44803086957849973955428867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59737449277133298607238489 44803086957849973955428867)
            ·
              refine ⟨67204630436774960933143301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44803086957849973955428867 67204630436774960933143301)
              ·
                refine ⟨12600868206895305174964369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67204630436774960933143301 12600868206895305174964369)
                ·
                  refine ⟨9450651155171478881223277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12600868206895305174964369 9450651155171478881223277)
                  ·
                    refine ⟨3543994183189304580458729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9450651155171478881223277 3543994183189304580458729)
                    ·
                      refine ⟨2657995637391978435344047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3543994183189304580458729 2657995637391978435344047)
                      ·
                        rfl

theorem cell23_5176428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_5176428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176428 prefixEnd_5176428 := by exact prefixLift 5176428
  have htrace : WordTrace (prefixWord ++ tailWord_5176428) baseStart_5176428 baseEnd_5176428 := by
    simpa [prefixWord, tailWord_5176428, baseEnd_5176428] using wordTrace_append hprefix tailTrace_5176428
  have hstable : (prefixWord ++ tailWord_5176428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176428).length < 2 ^ (prefixWord ++ tailWord_5176428).sum := by decide
  have hdescent : baseEnd_5176428 < baseStart_5176428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176451 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 1, 6]
def baseStart_5176451 : Nat := 118140960795 + 5176451 * 2 ^ 59
def prefixEnd_5176451 : Nat := 4983230072969 + 3 ^ 40 * 5176451 * 2
def baseEnd_5176451 : Nat := 886002482482343948452147

theorem tailTrace_5176451 : CollatzResearch.WordTrace tailWord_5176451 prefixEnd_5176451 886002482482343948452147 := by
  unfold tailWord_5176451
  simp only [CollatzResearch.WordTrace]
  refine ⟨188800678569609569291705207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125867119046406379527803471 188800678569609569291705207)
  ·
    refine ⟨283201017854414353937557811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188800678569609569291705207 283201017854414353937557811)
    ·
      refine ⟨424801526781621530906336717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283201017854414353937557811 424801526781621530906336717)
      ·
        refine ⟨159300572543108074089876269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424801526781621530906336717 159300572543108074089876269)
        ·
          refine ⟨59737714703665527783703601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159300572543108074089876269 59737714703665527783703601)
          ·
            refine ⟨44803286027749145837777701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59737714703665527783703601 44803286027749145837777701)
            ·
              refine ⟨8400616130202964844583319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44803286027749145837777701 8400616130202964844583319)
              ·
                refine ⟨12600924195304447266874979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8400616130202964844583319 12600924195304447266874979)
                ·
                  refine ⟨18901386292956670900312469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12600924195304447266874979 18901386292956670900312469)
                  ·
                    refine ⟨886002482482343948452147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18901386292956670900312469 886002482482343948452147)
                    ·
                      rfl

theorem cell23_5176451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 6].length) (baseStart_5176451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176451 prefixEnd_5176451 := by exact prefixLift 5176451
  have htrace : WordTrace (prefixWord ++ tailWord_5176451) baseStart_5176451 baseEnd_5176451 := by
    simpa [prefixWord, tailWord_5176451, baseEnd_5176451] using wordTrace_append hprefix tailTrace_5176451
  have hstable : (prefixWord ++ tailWord_5176451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176451).length < 2 ^ (prefixWord ++ tailWord_5176451).sum := by decide
  have hdescent : baseEnd_5176451 < baseStart_5176451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176458 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_5176458 : Nat := 118140960795 + 5176458 * 2 ^ 59
def prefixEnd_5176458 : Nat := 4983230072969 + 3 ^ 40 * 5176458 * 2
def baseEnd_5176458 : Nat := 2658011041811613317968909

theorem tailTrace_5176458 : CollatzResearch.WordTrace tailWord_5176458 prefixEnd_5176458 2658011041811613317968909 := by
  unfold tailWord_5176458
  simp only [CollatzResearch.WordTrace]
  refine ⟨47200233470146052371802507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125867289253722806324806685 47200233470146052371802507)
  ·
    refine ⟨70800350205219078557703761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47200233470146052371802507 70800350205219078557703761)
    ·
      refine ⟨53100262653914308918277821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70800350205219078557703761 53100262653914308918277821)
      ·
        refine ⟨19912598495217865844354183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53100262653914308918277821 19912598495217865844354183)
        ·
          refine ⟨29868897742826798766531275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19912598495217865844354183 29868897742826798766531275)
          ·
            refine ⟨44803346614240198149796913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29868897742826798766531275 44803346614240198149796913)
            ·
              refine ⟨33602509960680148612347685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44803346614240198149796913 33602509960680148612347685)
              ·
                refine ⟨6300470617627527864815191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33602509960680148612347685 6300470617627527864815191)
                ·
                  refine ⟨9450705926441291797222787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6300470617627527864815191 9450705926441291797222787)
                  ·
                    refine ⟨14176058889661937695834181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9450705926441291797222787 14176058889661937695834181)
                    ·
                      refine ⟨2658011041811613317968909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14176058889661937695834181 2658011041811613317968909)
                      ·
                        rfl

theorem cell23_5176458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_5176458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176458 prefixEnd_5176458 := by exact prefixLift 5176458
  have htrace : WordTrace (prefixWord ++ tailWord_5176458) baseStart_5176458 baseEnd_5176458 := by
    simpa [prefixWord, tailWord_5176458, baseEnd_5176458] using wordTrace_append hprefix tailTrace_5176458
  have hstable : (prefixWord ++ tailWord_5176458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176458).length < 2 ^ (prefixWord ++ tailWord_5176458).sum := by decide
  have hdescent : baseEnd_5176458 < baseStart_5176458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176462 : List Nat := [4, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_5176462 : Nat := 118140960795 + 5176462 * 2 ^ 59
def prefixEnd_5176462 : Nat := 4983230072969 + 3 ^ 40 * 5176462 * 2
def baseEnd_5176462 : Nat := 2658013095734231302318891

theorem tailTrace_5176462 : CollatzResearch.WordTrace tailWord_5176462 prefixEnd_5176462 2658013095734231302318891 := by
  unfold tailWord_5176462
  simp only [CollatzResearch.WordTrace]
  refine ⟨23600134971571214771294455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125867386515046478780237093 23600134971571214771294455)
  ·
    refine ⟨35400202457356822156941683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23600134971571214771294455 35400202457356822156941683)
    ·
      refine ⟨53100303686035233235412525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35400202457356822156941683 53100303686035233235412525)
      ·
        refine ⟨19912613882263212463279697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53100303686035233235412525 19912613882263212463279697)
        ·
          refine ⟨14934460411697409347459773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19912613882263212463279697 14934460411697409347459773)
          ·
            refine ⟨5600422654386528505297415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14934460411697409347459773 5600422654386528505297415)
            ·
              refine ⟨8400633981579792757946123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600422654386528505297415 8400633981579792757946123)
              ·
                refine ⟨12600950972369689136919185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8400633981579792757946123 12600950972369689136919185)
                ·
                  refine ⟨9450713229277266852689389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12600950972369689136919185 9450713229277266852689389)
                  ·
                    refine ⟨3544017460978975069758521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9450713229277266852689389 3544017460978975069758521)
                    ·
                      refine ⟨2658013095734231302318891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544017460978975069758521 2658013095734231302318891)
                      ·
                        rfl

theorem cell23_5176462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_5176462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176462 prefixEnd_5176462 := by exact prefixLift 5176462
  have htrace : WordTrace (prefixWord ++ tailWord_5176462) baseStart_5176462 baseEnd_5176462 := by
    simpa [prefixWord, tailWord_5176462, baseEnd_5176462] using wordTrace_append hprefix tailTrace_5176462
  have hstable : (prefixWord ++ tailWord_5176462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176462).length < 2 ^ (prefixWord ++ tailWord_5176462).sum := by decide
  have hdescent : baseEnd_5176462 < baseStart_5176462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176485 : List Nat := [1, 3, 1, 2, 1, 6, 1, 2, 2, 4]
def baseStart_5176485 : Nat := 118140960795 + 5176485 * 2 ^ 59
def prefixEnd_5176485 : Nat := 4983230072969 + 3 ^ 40 * 5176485 * 2
def baseEnd_5176485 : Nat := 886008301929761570777095

theorem tailTrace_5176485 : CollatzResearch.WordTrace tailWord_5176485 prefixEnd_5176485 886008301929761570777095 := by
  unfold tailWord_5176485
  simp only [CollatzResearch.WordTrace]
  refine ⟨188801918651486393098442909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125867945767657595398961939 188801918651486393098442909)
  ·
    refine ⟨70800719494307397411916091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188801918651486393098442909 70800719494307397411916091)
    ·
      refine ⟨106201079241461096117874137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70800719494307397411916091 106201079241461096117874137)
      ·
        refine ⟨79650809431095822088405603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106201079241461096117874137 79650809431095822088405603)
        ·
          refine ⟨119476214146643733132608405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79650809431095822088405603 119476214146643733132608405)
          ·
            refine ⟨5600447538123924990591019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119476214146643733132608405 5600447538123924990591019)
            ·
              refine ⟨8400671307185887485886529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600447538123924990591019 8400671307185887485886529)
              ·
                refine ⟨6300503480389415614414897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8400671307185887485886529 6300503480389415614414897)
                ·
                  refine ⟨4725377610292061710811173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6300503480389415614414897 4725377610292061710811173)
                  ·
                    refine ⟨886008301929761570777095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4725377610292061710811173 886008301929761570777095)
                    ·
                      rfl

theorem cell23_5176485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_5176485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176485 prefixEnd_5176485 := by exact prefixLift 5176485
  have htrace : WordTrace (prefixWord ++ tailWord_5176485) baseStart_5176485 baseEnd_5176485 := by
    simpa [prefixWord, tailWord_5176485, baseEnd_5176485] using wordTrace_append hprefix tailTrace_5176485
  have hstable : (prefixWord ++ tailWord_5176485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176485).length < 2 ^ (prefixWord ++ tailWord_5176485).sum := by decide
  have hdescent : baseEnd_5176485 < baseStart_5176485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176526 : List Nat := [4, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2]
def baseStart_5176526 : Nat := 118140960795 + 5176526 * 2 ^ 59
def prefixEnd_5176526 : Nat := 4983230072969 + 3 ^ 40 * 5176526 * 2
def baseEnd_5176526 : Nat := 2658045958496119051918597

theorem tailTrace_5176526 : CollatzResearch.WordTrace tailWord_5176526 prefixEnd_5176526 2658045958496119051918597 := by
  unfold tailWord_5176526
  simp only [CollatzResearch.WordTrace]
  refine ⟨23600426755542232137585679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125868942696225238067123621 23600426755542232137585679)
  ·
    refine ⟨35400640133313348206378519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23600426755542232137585679 35400640133313348206378519)
    ·
      refine ⟨53100960199970022309567779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35400640133313348206378519 53100960199970022309567779)
      ·
        refine ⟨79651440299955033464351669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53100960199970022309567779 79651440299955033464351669)
        ·
          refine ⟨7467322528120784387282969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79651440299955033464351669 7467322528120784387282969)
          ·
            refine ⟨5600491896090588290462227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7467322528120784387282969 5600491896090588290462227)
            ·
              refine ⟨8400737844135882435693341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600491896090588290462227 8400737844135882435693341)
              ·
                refine ⟨3150276691550955913385003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8400737844135882435693341 3150276691550955913385003)
                ·
                  refine ⟨4725415037326433870077505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150276691550955913385003 4725415037326433870077505)
                  ·
                    refine ⟨3544061277994825402558129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4725415037326433870077505 3544061277994825402558129)
                    ·
                      refine ⟨2658045958496119051918597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544061277994825402558129 2658045958496119051918597)
                      ·
                        rfl

theorem cell23_5176526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_5176526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176526 prefixEnd_5176526 := by exact prefixLift 5176526
  have htrace : WordTrace (prefixWord ++ tailWord_5176526) baseStart_5176526 baseEnd_5176526 := by
    simpa [prefixWord, tailWord_5176526, baseEnd_5176526] using wordTrace_append hprefix tailTrace_5176526
  have hstable : (prefixWord ++ tailWord_5176526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176526).length < 2 ^ (prefixWord ++ tailWord_5176526).sum := by decide
  have hdescent : baseEnd_5176526 < baseStart_5176526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176535 : List Nat := [1, 1, 3, 2, 1, 2, 4, 3, 1, 3, 2]
def baseStart_5176535 : Nat := 118140960795 + 5176535 * 2 ^ 59
def prefixEnd_5176535 : Nat := 4983230072969 + 3 ^ 40 * 5176535 * 2
def baseEnd_5176535 : Nat := 2658050579822009516706055

theorem tailTrace_5176535 : CollatzResearch.WordTrace tailWord_5176535 prefixEnd_5176535 2658050579822009516706055 := by
  unfold tailWord_5176535
  simp only [CollatzResearch.WordTrace]
  refine ⟨188803742301305251637763059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125869161534203501091842039 188803742301305251637763059)
  ·
    refine ⟨283205613451957877456644589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188803742301305251637763059 283205613451957877456644589)
    ·
      refine ⟨106202105044484204046241721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283205613451957877456644589 106202105044484204046241721)
      ·
        refine ⟨79651578783363153034681291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106202105044484204046241721 79651578783363153034681291)
        ·
          refine ⟨119477368175044729552021937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79651578783363153034681291 119477368175044729552021937)
          ·
            refine ⟨89608026131283547164016453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119477368175044729552021937 89608026131283547164016453)
            ·
              refine ⟨16801504899615665093253085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89608026131283547164016453 16801504899615665093253085)
              ·
                refine ⟨6300564337355874409969907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16801504899615665093253085 6300564337355874409969907)
                ·
                  refine ⟨9450846506033811614954861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6300564337355874409969907 9450846506033811614954861)
                  ·
                    refine ⟨3544067439762679355608073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9450846506033811614954861 3544067439762679355608073)
                    ·
                      refine ⟨2658050579822009516706055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544067439762679355608073 2658050579822009516706055)
                      ·
                        rfl

theorem cell23_5176535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_5176535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176535 prefixEnd_5176535 := by exact prefixLift 5176535
  have htrace : WordTrace (prefixWord ++ tailWord_5176535) baseStart_5176535 baseEnd_5176535 := by
    simpa [prefixWord, tailWord_5176535, baseEnd_5176535] using wordTrace_append hprefix tailTrace_5176535
  have hstable : (prefixWord ++ tailWord_5176535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176535).length < 2 ^ (prefixWord ++ tailWord_5176535).sum := by decide
  have hdescent : baseEnd_5176535 < baseStart_5176535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176559 : List Nat := [1, 1, 2, 1, 7, 2, 2, 1, 2, 1, 3]
def baseStart_5176559 : Nat := 118140960795 + 5176559 * 2 ^ 59
def prefixEnd_5176559 : Nat := 4983230072969 + 3 ^ 40 * 5176559 * 2
def baseEnd_5176559 : Nat := 2658062903357717422805945

theorem tailTrace_5176559 : CollatzResearch.WordTrace tailWord_5176559 prefixEnd_5176559 2658062903357717422805945 := by
  unfold tailWord_5176559
  simp only [CollatzResearch.WordTrace]
  refine ⟨188804617653218303736636731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125869745102145535824424487 188804617653218303736636731)
  ·
    refine ⟨283206926479827455604955097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188804617653218303736636731 283206926479827455604955097)
    ·
      refine ⟨212405194859870591703716323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283206926479827455604955097 212405194859870591703716323)
      ·
        refine ⟨318607792289805887555574485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212405194859870591703716323 318607792289805887555574485)
        ·
          refine ⟨7467370131792325489583777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 318607792289805887555574485 7467370131792325489583777)
          ·
            refine ⟨5600527598844244117187833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7467370131792325489583777 5600527598844244117187833)
            ·
              refine ⟨4200395699133183087890875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5600527598844244117187833 4200395699133183087890875)
              ·
                refine ⟨6300593548699774631836313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4200395699133183087890875 6300593548699774631836313)
                ·
                  refine ⟨4725445161524830973877235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6300593548699774631836313 4725445161524830973877235)
                  ·
                    refine ⟨7088167742287246460815853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4725445161524830973877235 7088167742287246460815853)
                    ·
                      refine ⟨2658062903357717422805945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7088167742287246460815853 2658062903357717422805945)
                      ·
                        rfl

theorem cell23_5176559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 2, 1, 3].length) (baseStart_5176559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176559 prefixEnd_5176559 := by exact prefixLift 5176559
  have htrace : WordTrace (prefixWord ++ tailWord_5176559) baseStart_5176559 baseEnd_5176559 := by
    simpa [prefixWord, tailWord_5176559, baseEnd_5176559] using wordTrace_append hprefix tailTrace_5176559
  have hstable : (prefixWord ++ tailWord_5176559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176559).length < 2 ^ (prefixWord ++ tailWord_5176559).sum := by decide
  have hdescent : baseEnd_5176559 < baseStart_5176559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176561 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_5176561 : Nat := 118140960795 + 5176561 * 2 ^ 59
def prefixEnd_5176561 : Nat := 4983230072969 + 3 ^ 40 * 5176561 * 2
def baseEnd_5176561 : Nat := 2658063930319026414980935

theorem tailTrace_5176561 : CollatzResearch.WordTrace tailWord_5176561 prefixEnd_5176561 2658063930319026414980935 := by
  unfold tailWord_5176561
  simp only [CollatzResearch.WordTrace]
  refine ⟨188804690599211058078209537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125869793732807372052139691 188804690599211058078209537)
  ·
    refine ⟨141603517949408293558657153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188804690599211058078209537 141603517949408293558657153)
    ·
      refine ⟨106202638462056220168992865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141603517949408293558657153 106202638462056220168992865)
      ·
        refine ⟨79651978846542165126744649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106202638462056220168992865 79651978846542165126744649)
        ·
          refine ⟨59738984134906623845058487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79651978846542165126744649 59738984134906623845058487)
          ·
            refine ⟨89608476202359935767587731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59738984134906623845058487 89608476202359935767587731)
            ·
              refine ⟨134412714303539903651381597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89608476202359935767587731 134412714303539903651381597)
              ·
                refine ⟨50404767863827463869268099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134412714303539903651381597 50404767863827463869268099)
                ·
                  refine ⟨75607151795741195803902149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50404767863827463869268099 75607151795741195803902149)
                  ·
                    refine ⟨14176340961701474213231653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75607151795741195803902149 14176340961701474213231653)
                    ·
                      refine ⟨2658063930319026414980935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14176340961701474213231653 2658063930319026414980935)
                      ·
                        rfl

theorem cell23_5176561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_5176561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176561 prefixEnd_5176561 := by exact prefixLift 5176561
  have htrace : WordTrace (prefixWord ++ tailWord_5176561) baseStart_5176561 baseEnd_5176561 := by
    simpa [prefixWord, tailWord_5176561, baseEnd_5176561] using wordTrace_append hprefix tailTrace_5176561
  have hstable : (prefixWord ++ tailWord_5176561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176561).length < 2 ^ (prefixWord ++ tailWord_5176561).sum := by decide
  have hdescent : baseEnd_5176561 < baseStart_5176561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176648 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 7, 4]
def baseStart_5176648 : Nat := 118140960795 + 5176648 * 2 ^ 59
def prefixEnd_5176648 : Nat := 4983230072969 + 3 ^ 40 * 5176648 * 2
def baseEnd_5176648 : Nat := 886036201045322524864345

theorem tailTrace_5176648 : CollatzResearch.WordTrace tailWord_5176648 prefixEnd_5176648 886036201045322524864345 := by
  unfold tailWord_5176648
  simp only [CollatzResearch.WordTrace]
  refine ⟨94403931874947935968313299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125871909166597247957751065 94403931874947935968313299)
  ·
    refine ⟨141605897812421903952469949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94403931874947935968313299 141605897812421903952469949)
    ·
      refine ⟨53102211679658213982176231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141605897812421903952469949 53102211679658213982176231)
      ·
        refine ⟨79653317519487320973264347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53102211679658213982176231 79653317519487320973264347)
        ·
          refine ⟨119479976279230981459896521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79653317519487320973264347 119479976279230981459896521)
          ·
            refine ⟨89609982209423236094922391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119479976279230981459896521 89609982209423236094922391)
            ·
              refine ⟨134414973314134854142383587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89609982209423236094922391 134414973314134854142383587)
              ·
                refine ⟨201622459971202281213575381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134414973314134854142383587 201622459971202281213575381)
                ·
                  refine ⟨4725526405575053465943173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 201622459971202281213575381 4725526405575053465943173)
                  ·
                    refine ⟨886036201045322524864345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4725526405575053465943173 886036201045322524864345)
                    ·
                      rfl

theorem cell23_5176648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_5176648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176648 prefixEnd_5176648 := by exact prefixLift 5176648
  have htrace : WordTrace (prefixWord ++ tailWord_5176648) baseStart_5176648 baseEnd_5176648 := by
    simpa [prefixWord, tailWord_5176648, baseEnd_5176648] using wordTrace_append hprefix tailTrace_5176648
  have hstable : (prefixWord ++ tailWord_5176648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176648).length < 2 ^ (prefixWord ++ tailWord_5176648).sum := by decide
  have hdescent : baseEnd_5176648 < baseStart_5176648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176688 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 3]
def baseStart_5176688 : Nat := 118140960795 + 5176688 * 2 ^ 59
def prefixEnd_5176688 : Nat := 4983230072969 + 3 ^ 40 * 5176688 * 2
def baseEnd_5176688 : Nat := 2658129142362147418092851

theorem tailTrace_5176688 : CollatzResearch.WordTrace tailWord_5176688 prefixEnd_5176688 2658129142362147418092851 := by
  unfold tailWord_5176688
  simp only [CollatzResearch.WordTrace]
  refine ⟨94404661334875479384041359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125872881779833972512055145 94404661334875479384041359)
  ·
    refine ⟨141606992002313219076062039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94404661334875479384041359 141606992002313219076062039)
    ·
      refine ⟨212410488003469828614093059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141606992002313219076062039 212410488003469828614093059)
      ·
        refine ⟨318615732005204742921139589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212410488003469828614093059 318615732005204742921139589)
        ·
          refine ⟨59740449750975889297713673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318615732005204742921139589 59740449750975889297713673)
          ·
            refine ⟨44805337313231916973285255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59740449750975889297713673 44805337313231916973285255)
            ·
              refine ⟨67208005969847875459927883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44805337313231916973285255 67208005969847875459927883)
              ·
                refine ⟨100812008954771813189891825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67208005969847875459927883 100812008954771813189891825)
                ·
                  refine ⟨75609006716078859892418869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100812008954771813189891825 75609006716078859892418869)
                  ·
                    refine ⟨7088344379632393114914269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75609006716078859892418869 7088344379632393114914269)
                    ·
                      refine ⟨2658129142362147418092851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7088344379632393114914269 2658129142362147418092851)
                      ·
                        rfl

theorem cell23_5176688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 3].length) (baseStart_5176688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176688 prefixEnd_5176688 := by exact prefixLift 5176688
  have htrace : WordTrace (prefixWord ++ tailWord_5176688) baseStart_5176688 baseEnd_5176688 := by
    simpa [prefixWord, tailWord_5176688, baseEnd_5176688] using wordTrace_append hprefix tailTrace_5176688
  have hstable : (prefixWord ++ tailWord_5176688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176688).length < 2 ^ (prefixWord ++ tailWord_5176688).sum := by decide
  have hdescent : baseEnd_5176688 < baseStart_5176688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176748 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 5]
def baseStart_5176748 : Nat := 118140960795 + 5176748 * 2 ^ 59
def prefixEnd_5176748 : Nat := 4983230072969 + 3 ^ 40 * 5176748 * 2
def baseEnd_5176748 : Nat := 2658159951201417183342575

theorem tailTrace_5176748 : CollatzResearch.WordTrace tailWord_5176748 prefixEnd_5176748 2658159951201417183342575 := by
  unfold tailWord_5176748
  simp only [CollatzResearch.WordTrace]
  refine ⟨94405755524766794507633449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125874340699689059343511265 94405755524766794507633449)
  ·
    refine ⟨70804316643575095880725087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94405755524766794507633449 70804316643575095880725087)
    ·
      refine ⟨106206474965362643821087631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70804316643575095880725087 106206474965362643821087631)
      ·
        refine ⟨159309712448043965731631447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106206474965362643821087631 159309712448043965731631447)
        ·
          refine ⟨238964568672065948597447171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159309712448043965731631447 238964568672065948597447171)
          ·
            refine ⟨358446853008098922896170757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238964568672065948597447171 358446853008098922896170757)
            ·
              refine ⟨67208784939018548043032017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 358446853008098922896170757 67208784939018548043032017)
              ·
                refine ⟨50406588704263911032274013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67208784939018548043032017 50406588704263911032274013)
                ·
                  refine ⟨18902470764098966637102755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50406588704263911032274013 18902470764098966637102755)
                  ·
                    refine ⟨28353706146148449955654133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18902470764098966637102755 28353706146148449955654133)
                    ·
                      refine ⟨2658159951201417183342575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28353706146148449955654133 2658159951201417183342575)
                      ·
                        rfl

theorem cell23_5176748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_5176748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176748 prefixEnd_5176748 := by exact prefixLift 5176748
  have htrace : WordTrace (prefixWord ++ tailWord_5176748) baseStart_5176748 baseEnd_5176748 := by
    simpa [prefixWord, tailWord_5176748, baseEnd_5176748] using wordTrace_append hprefix tailTrace_5176748
  have hstable : (prefixWord ++ tailWord_5176748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176748).length < 2 ^ (prefixWord ++ tailWord_5176748).sum := by decide
  have hdescent : baseEnd_5176748 < baseStart_5176748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176749 : List Nat := [1, 5, 2, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5176749 : Nat := 118140960795 + 5176749 * 2 ^ 59
def prefixEnd_5176749 : Nat := 4983230072969 + 3 ^ 40 * 5176749 * 2
def baseEnd_5176749 : Nat := 2658160464682071679430071

theorem tailTrace_5176749 : CollatzResearch.WordTrace tailWord_5176749 prefixEnd_5176749 2658160464682071679430071 := by
  unfold tailWord_5176749
  simp only [CollatzResearch.WordTrace]
  refine ⟨188811547522529966186053301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125874365015019977457368867 188811547522529966186053301)
  ·
    refine ⟨17701082580237184329942497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188811547522529966186053301 17701082580237184329942497)
    ·
      refine ⟨13275811935177888247456873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17701082580237184329942497 13275811935177888247456873)
      ·
        refine ⟨9956858951383416185592655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13275811935177888247456873 9956858951383416185592655)
        ·
          refine ⟨14935288427075124278388983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9956858951383416185592655 14935288427075124278388983)
          ·
            refine ⟨22402932640612686417583475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14935288427075124278388983 22402932640612686417583475)
            ·
              refine ⟨33604398960919029626375213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22402932640612686417583475 33604398960919029626375213)
              ·
                refine ⟨12601649610344636109890705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33604398960919029626375213 12601649610344636109890705)
                ·
                  refine ⟨9451237207758477082418029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12601649610344636109890705 9451237207758477082418029)
                  ·
                    refine ⟨3544213952909428905906761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9451237207758477082418029 3544213952909428905906761)
                    ·
                      refine ⟨2658160464682071679430071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544213952909428905906761 2658160464682071679430071)
                      ·
                        rfl

theorem cell23_5176749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5176749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176749 prefixEnd_5176749 := by exact prefixLift 5176749
  have htrace : WordTrace (prefixWord ++ tailWord_5176749) baseStart_5176749 baseEnd_5176749 := by
    simpa [prefixWord, tailWord_5176749, baseEnd_5176749] using wordTrace_append hprefix tailTrace_5176749
  have hstable : (prefixWord ++ tailWord_5176749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176749).length < 2 ^ (prefixWord ++ tailWord_5176749).sum := by decide
  have hdescent : baseEnd_5176749 < baseStart_5176749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176813 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5176813 : Nat := 118140960795 + 5176813 * 2 ^ 59
def prefixEnd_5176813 : Nat := 4983230072969 + 3 ^ 40 * 5176813 * 2
def baseEnd_5176813 : Nat := 2658193327443959429029777

theorem tailTrace_5176813 : CollatzResearch.WordTrace tailWord_5176813 prefixEnd_5176813 2658193327443959429029777 := by
  unfold tailWord_5176813
  simp only [CollatzResearch.WordTrace]
  refine ⟨188813881794298105116383093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125875921196198736744255395 188813881794298105116383093)
  ·
    refine ⟨17701301418215447354660915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188813881794298105116383093 17701301418215447354660915)
    ·
      refine ⟨26551952127323171031991373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17701301418215447354660915 26551952127323171031991373)
      ·
        refine ⟨9956982047746189136996765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26551952127323171031991373 9956982047746189136996765)
        ·
          refine ⟨3733868267904820926373787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9956982047746189136996765 3733868267904820926373787)
          ·
            refine ⟨5600802401857231389560681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733868267904820926373787 5600802401857231389560681)
            ·
              refine ⟨4200601801392923542170511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5600802401857231389560681 4200601801392923542170511)
              ·
                refine ⟨6300902702089385313255767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4200601801392923542170511 6300902702089385313255767)
                ·
                  refine ⟨9451354053134077969883651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6300902702089385313255767 9451354053134077969883651)
                  ·
                    refine ⟨14177031079701116954825477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9451354053134077969883651 14177031079701116954825477)
                    ·
                      refine ⟨2658193327443959429029777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14177031079701116954825477 2658193327443959429029777)
                      ·
                        rfl

theorem cell23_5176813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5176813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176813 prefixEnd_5176813 := by exact prefixLift 5176813
  have htrace : WordTrace (prefixWord ++ tailWord_5176813) baseStart_5176813 baseEnd_5176813 := by
    simpa [prefixWord, tailWord_5176813, baseEnd_5176813] using wordTrace_append hprefix tailTrace_5176813
  have hstable : (prefixWord ++ tailWord_5176813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176813).length < 2 ^ (prefixWord ++ tailWord_5176813).sum := by decide
  have hdescent : baseEnd_5176813 < baseStart_5176813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176829 : List Nat := [1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_5176829 : Nat := 118140960795 + 5176829 * 2 ^ 59
def prefixEnd_5176829 : Nat := 4983230072969 + 3 ^ 40 * 5176829 * 2
def baseEnd_5176829 : Nat := 2658201543134431366429703

theorem tailTrace_5176829 : CollatzResearch.WordTrace tailWord_5176829 prefixEnd_5176829 2658201543134431366429703 := by
  unfold tailWord_5176829
  simp only [CollatzResearch.WordTrace]
  refine ⟨188814465362240139848965541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125876310241493426565977027 188814465362240139848965541)
  ·
    refine ⟨35402712255420026221681039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 188814465362240139848965541 35402712255420026221681039)
    ·
      refine ⟨53104068383130039332521559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35402712255420026221681039 53104068383130039332521559)
      ·
        refine ⟨79656102574695058998782339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53104068383130039332521559 79656102574695058998782339)
        ·
          refine ⟨119484153862042588498173509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79656102574695058998782339 119484153862042588498173509)
          ·
            refine ⟨22403278849132985343407533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119484153862042588498173509 22403278849132985343407533)
            ·
              refine ⟨8401229568424869503777825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22403278849132985343407533 8401229568424869503777825)
              ·
                refine ⟨6300922176318652127833369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8401229568424869503777825 6300922176318652127833369)
                ·
                  refine ⟨4725691632238989095875027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6300922176318652127833369 4725691632238989095875027)
                  ·
                    refine ⟨7088537448358483643812541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4725691632238989095875027 7088537448358483643812541)
                    ·
                      refine ⟨2658201543134431366429703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7088537448358483643812541 2658201543134431366429703)
                      ·
                        rfl

theorem cell23_5176829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_5176829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176829 prefixEnd_5176829 := by exact prefixLift 5176829
  have htrace : WordTrace (prefixWord ++ tailWord_5176829) baseStart_5176829 baseEnd_5176829 := by
    simpa [prefixWord, tailWord_5176829, baseEnd_5176829] using wordTrace_append hprefix tailTrace_5176829
  have hstable : (prefixWord ++ tailWord_5176829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176829).length < 2 ^ (prefixWord ++ tailWord_5176829).sum := by decide
  have hdescent : baseEnd_5176829 < baseStart_5176829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176846 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_5176846 : Nat := 118140960795 + 5176846 * 2 ^ 59
def prefixEnd_5176846 : Nat := 4983230072969 + 3 ^ 40 * 5176846 * 2
def baseEnd_5176846 : Nat := 2658210272305557799917125

theorem tailTrace_5176846 : CollatzResearch.WordTrace tailWord_5176846 prefixEnd_5176846 2658210272305557799917125 := by
  unfold tailWord_5176846
  simp only [CollatzResearch.WordTrace]
  refine ⟨23601885675397318969041799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125876723602119034501556261 23601885675397318969041799)
  ·
    refine ⟨35402828513095978453562699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23601885675397318969041799 35402828513095978453562699)
    ·
      refine ⟨53104242769643967680344049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35402828513095978453562699 53104242769643967680344049)
      ·
        refine ⟨39828182077232975760258037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53104242769643967680344049 39828182077232975760258037)
        ·
          refine ⟨3733892069740591477524191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39828182077232975760258037 3733892069740591477524191)
          ·
            refine ⟨5600838104610887216286287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3733892069740591477524191 5600838104610887216286287)
            ·
              refine ⟨8401257156916330824429431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5600838104610887216286287 8401257156916330824429431)
              ·
                refine ⟨12601885735374496236644147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8401257156916330824429431 12601885735374496236644147)
                ·
                  refine ⟨18902828603061744354966221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12601885735374496236644147 18902828603061744354966221)
                  ·
                    refine ⟨7088560726148154133112333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18902828603061744354966221 7088560726148154133112333)
                    ·
                      refine ⟨2658210272305557799917125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7088560726148154133112333 2658210272305557799917125)
                      ·
                        rfl

theorem cell23_5176846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_5176846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176846 prefixEnd_5176846 := by exact prefixLift 5176846
  have htrace : WordTrace (prefixWord ++ tailWord_5176846) baseStart_5176846 baseEnd_5176846 := by
    simpa [prefixWord, tailWord_5176846, baseEnd_5176846] using wordTrace_append hprefix tailTrace_5176846
  have hstable : (prefixWord ++ tailWord_5176846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176846).length < 2 ^ (prefixWord ++ tailWord_5176846).sum := by decide
  have hdescent : baseEnd_5176846 < baseStart_5176846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5176856 : List Nat := [2, 1, 2, 3, 4, 1, 2, 2, 1, 3, 2]
def baseStart_5176856 : Nat := 118140960795 + 5176856 * 2 ^ 59
def prefixEnd_5176856 : Nat := 4983230072969 + 3 ^ 40 * 5176856 * 2
def baseEnd_5176856 : Nat := 2658215407112102760792079

theorem tailTrace_5176856 : CollatzResearch.WordTrace tailWord_5176856 prefixEnd_5176856 2658215407112102760792079 := by
  unfold tailWord_5176856
  simp only [CollatzResearch.WordTrace]
  refine ⟨94407725066571161730099211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125876966755428215640132281 94407725066571161730099211)
  ·
    refine ⟨141611587599856742595148817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94407725066571161730099211 141611587599856742595148817)
    ·
      refine ⟨106208690699892556946361613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141611587599856742595148817 106208690699892556946361613)
      ·
        refine ⟨39828259012459708854885605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106208690699892556946361613 39828259012459708854885605)
        ·
          refine ⟨7467798564836195410291051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39828259012459708854885605 7467798564836195410291051)
          ·
            refine ⟨11201697847254293115436577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7467798564836195410291051 11201697847254293115436577)
            ·
              refine ⟨8401273385440719836577433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11201697847254293115436577 8401273385440719836577433)
              ·
                refine ⟨6300955039080539877433075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8401273385440719836577433 6300955039080539877433075)
                ·
                  refine ⟨9451432558620809816149613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6300955039080539877433075 9451432558620809816149613)
                  ·
                    refine ⟨3544287209482803681056105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9451432558620809816149613 3544287209482803681056105)
                    ·
                      refine ⟨2658215407112102760792079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544287209482803681056105 2658215407112102760792079)
                      ·
                        rfl

theorem cell23_5176856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_5176856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5176856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5176856 prefixEnd_5176856 := by exact prefixLift 5176856
  have htrace : WordTrace (prefixWord ++ tailWord_5176856) baseStart_5176856 baseEnd_5176856 := by
    simpa [prefixWord, tailWord_5176856, baseEnd_5176856] using wordTrace_append hprefix tailTrace_5176856
  have hstable : (prefixWord ++ tailWord_5176856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5176856).length < 2 ^ (prefixWord ++ tailWord_5176856).sum := by decide
  have hdescent : baseEnd_5176856 < baseStart_5176856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5176856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177049 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 4]
def baseStart_5177049 : Nat := 118140960795 + 5177049 * 2 ^ 59
def prefixEnd_5177049 : Nat := 4983230072969 + 3 ^ 40 * 5177049 * 2
def baseEnd_5177049 : Nat := 2658314508878420505678691

theorem tailTrace_5177049 : CollatzResearch.WordTrace tailWord_5177049 prefixEnd_5177049 2658314508878420505678691 := by
  unfold tailWord_5177049
  simp only [CollatzResearch.WordTrace]
  refine ⟨188822489421443117421974201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125881659614295411614649467 188822489421443117421974201)
  ·
    refine ⟨141616867066082338066480651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188822489421443117421974201 141616867066082338066480651)
    ·
      refine ⟨212425300599123507099720977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141616867066082338066480651 212425300599123507099720977)
      ·
        refine ⟨159318975449342630324790733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212425300599123507099720977 159318975449342630324790733)
        ·
          refine ⟨59744615793503486371796525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159318975449342630324790733 59744615793503486371796525)
          ·
            refine ⟨22404230922563807389423697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59744615793503486371796525 22404230922563807389423697)
            ·
              refine ⟨16803173191922855542067773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22404230922563807389423697 16803173191922855542067773)
              ·
                refine ⟨6301189946971070828275415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16803173191922855542067773 6301189946971070828275415)
                ·
                  refine ⟨9451784920456606242413123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6301189946971070828275415 9451784920456606242413123)
                  ·
                    refine ⟨14177677380684909363619685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9451784920456606242413123 14177677380684909363619685)
                    ·
                      refine ⟨2658314508878420505678691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14177677380684909363619685 2658314508878420505678691)
                      ·
                        rfl

theorem cell23_5177049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_5177049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177049 prefixEnd_5177049 := by exact prefixLift 5177049
  have htrace : WordTrace (prefixWord ++ tailWord_5177049) baseStart_5177049 baseEnd_5177049 := by
    simpa [prefixWord, tailWord_5177049, baseEnd_5177049] using wordTrace_append hprefix tailTrace_5177049
  have hstable : (prefixWord ++ tailWord_5177049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177049).length < 2 ^ (prefixWord ++ tailWord_5177049).sum := by decide
  have hdescent : baseEnd_5177049 < baseStart_5177049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177069 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5177069 : Nat := 118140960795 + 5177069 * 2 ^ 59
def prefixEnd_5177069 : Nat := 4983230072969 + 3 ^ 40 * 5177069 * 2
def baseEnd_5177069 : Nat := 2658324778491510427428599

theorem tailTrace_5177069 : CollatzResearch.WordTrace tailWord_5177069 prefixEnd_5177069 2658324778491510427428599 := by
  unfold tailWord_5177069
  simp only [CollatzResearch.WordTrace]
  refine ⟨188823218881370660837702261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125882145920913773891801507 188823218881370660837702261)
  ·
    refine ⟨17702176770128499453534587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 188823218881370660837702261 17702176770128499453534587)
    ·
      refine ⟨26553265155192749180301881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17702176770128499453534587 26553265155192749180301881)
      ·
        refine ⟨19914948866394561885226411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26553265155192749180301881 19914948866394561885226411)
        ·
          refine ⟨29872423299591842827839617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19914948866394561885226411 29872423299591842827839617)
          ·
            refine ⟨22404317474693882120879713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29872423299591842827839617 22404317474693882120879713)
            ·
              refine ⟨16803238106020411590659785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22404317474693882120879713 16803238106020411590659785)
              ·
                refine ⟨12602428579515308692994839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16803238106020411590659785 12602428579515308692994839)
                ·
                  refine ⟨18903642869272963039492259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12602428579515308692994839 18903642869272963039492259)
                  ·
                    refine ⟨28355464303909444559238389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18903642869272963039492259 28355464303909444559238389)
                    ·
                      refine ⟨2658324778491510427428599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28355464303909444559238389 2658324778491510427428599)
                      ·
                        rfl

theorem cell23_5177069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5177069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177069 prefixEnd_5177069 := by exact prefixLift 5177069
  have htrace : WordTrace (prefixWord ++ tailWord_5177069) baseStart_5177069 baseEnd_5177069 := by
    simpa [prefixWord, tailWord_5177069, baseEnd_5177069] using wordTrace_append hprefix tailTrace_5177069
  have hstable : (prefixWord ++ tailWord_5177069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177069).length < 2 ^ (prefixWord ++ tailWord_5177069).sum := by decide
  have hdescent : baseEnd_5177069 < baseStart_5177069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177099 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 3]
def baseStart_5177099 : Nat := 118140960795 + 5177099 * 2 ^ 59
def prefixEnd_5177099 : Nat := 4983230072969 + 3 ^ 40 * 5177099 * 2
def baseEnd_5177099 : Nat := 2658340182911145310053461

theorem tailTrace_5177099 : CollatzResearch.WordTrace tailWord_5177099 prefixEnd_5177099 2658340182911145310053461 := by
  unfold tailWord_5177099
  simp only [CollatzResearch.WordTrace]
  refine ⟨188824313071261975961294351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125882875380841317307529567 188824313071261975961294351)
  ·
    refine ⟨283236469606892963941941527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188824313071261975961294351 283236469606892963941941527)
    ·
      refine ⟨424854704410339445912912291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283236469606892963941941527 424854704410339445912912291)
      ·
        refine ⟨637282056615509168869368437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424854704410339445912912291 637282056615509168869368437)
        ·
          refine ⟨59745192807703984581503291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 637282056615509168869368437 59745192807703984581503291)
          ·
            refine ⟨89617789211555976872254937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59745192807703984581503291 89617789211555976872254937)
            ·
              refine ⟨67213341908666982654191203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89617789211555976872254937 67213341908666982654191203)
              ·
                refine ⟨100820012863000473981286805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67213341908666982654191203 100820012863000473981286805)
                ·
                  refine ⟨4725938102953147217872819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100820012863000473981286805 4725938102953147217872819)
                  ·
                    refine ⟨7088907154429720826809229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4725938102953147217872819 7088907154429720826809229)
                    ·
                      refine ⟨2658340182911145310053461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7088907154429720826809229 2658340182911145310053461)
                      ·
                        rfl

theorem cell23_5177099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 3].length) (baseStart_5177099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177099 prefixEnd_5177099 := by exact prefixLift 5177099
  have htrace : WordTrace (prefixWord ++ tailWord_5177099) baseStart_5177099 baseEnd_5177099 := by
    simpa [prefixWord, tailWord_5177099, baseEnd_5177099] using wordTrace_append hprefix tailTrace_5177099
  have hstable : (prefixWord ++ tailWord_5177099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177099).length < 2 ^ (prefixWord ++ tailWord_5177099).sum := by decide
  have hdescent : baseEnd_5177099 < baseStart_5177099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177112 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5177112 : Nat := 118140960795 + 5177112 * 2 ^ 59
def prefixEnd_5177112 : Nat := 4983230072969 + 3 ^ 40 * 5177112 * 2
def baseEnd_5177112 : Nat := 2658346858159653759190901

theorem tailTrace_5177112 : CollatzResearch.WordTrace tailWord_5177112 prefixEnd_5177112 2658346858159653759190901 := by
  unfold tailWord_5177112
  simp only [CollatzResearch.WordTrace]
  refine ⟨94412393610107439590758795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125883191480143252787678393 94412393610107439590758795)
  ·
    refine ⟨141618590415161159386138193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94412393610107439590758795 141618590415161159386138193)
    ·
      refine ⟨106213942811370869539603645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141618590415161159386138193 106213942811370869539603645)
      ·
        refine ⟨39830228554264076077351367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106213942811370869539603645 39830228554264076077351367)
        ·
          refine ⟨59745342831396114116027051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39830228554264076077351367 59745342831396114116027051)
          ·
            refine ⟨89618014247094171174040577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59745342831396114116027051 89618014247094171174040577)
            ·
              refine ⟨67213510685320628380530433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89618014247094171174040577 67213510685320628380530433)
              ·
                refine ⟨50410133013990471285397825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67213510685320628380530433 50410133013990471285397825)
                ·
                  refine ⟨37807599760492853464048369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50410133013990471285397825 37807599760492853464048369)
                  ·
                    refine ⟨28355699820369640098036277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37807599760492853464048369 28355699820369640098036277)
                    ·
                      refine ⟨2658346858159653759190901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28355699820369640098036277 2658346858159653759190901)
                      ·
                        rfl

theorem cell23_5177112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5177112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177112 prefixEnd_5177112 := by exact prefixLift 5177112
  have htrace : WordTrace (prefixWord ++ tailWord_5177112) baseStart_5177112 baseEnd_5177112 := by
    simpa [prefixWord, tailWord_5177112, baseEnd_5177112] using wordTrace_append hprefix tailTrace_5177112
  have hstable : (prefixWord ++ tailWord_5177112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177112).length < 2 ^ (prefixWord ++ tailWord_5177112).sum := by decide
  have hdescent : baseEnd_5177112 < baseStart_5177112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177132 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 1, 8]
def baseStart_5177132 : Nat := 118140960795 + 5177132 * 2 ^ 59
def prefixEnd_5177132 : Nat := 4983230072969 + 3 ^ 40 * 5177132 * 2
def baseEnd_5177132 : Nat := 886119042590914560313603

theorem tailTrace_5177132 : CollatzResearch.WordTrace tailWord_5177132 prefixEnd_5177132 886119042590914560313603 := by
  unfold tailWord_5177132
  simp only [CollatzResearch.WordTrace]
  refine ⟨94412758340071211298622825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125883677786761615064830433 94412758340071211298622825)
  ·
    refine ⟨70809568755053408473967119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94412758340071211298622825 70809568755053408473967119)
    ·
      refine ⟨106214353132580112710950679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70809568755053408473967119 106214353132580112710950679)
      ·
        refine ⟨159321529698870169066426019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106214353132580112710950679 159321529698870169066426019)
        ·
          refine ⟨238982294548305253599639029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159321529698870169066426019 238982294548305253599639029)
          ·
            refine ⟨22404590113903617524966159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 238982294548305253599639029 22404590113903617524966159)
            ·
              refine ⟨33606885170855426287449239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22404590113903617524966159 33606885170855426287449239)
              ·
                refine ⟨50410327756283139431173859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33606885170855426287449239 50410327756283139431173859)
                ·
                  refine ⟨75615491634424709146760789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50410327756283139431173859 75615491634424709146760789)
                  ·
                    refine ⟨886119042590914560313603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75615491634424709146760789 886119042590914560313603)
                    ·
                      rfl

theorem cell23_5177132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 8].length) (baseStart_5177132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177132 prefixEnd_5177132 := by exact prefixLift 5177132
  have htrace : WordTrace (prefixWord ++ tailWord_5177132) baseStart_5177132 baseEnd_5177132 := by
    simpa [prefixWord, tailWord_5177132, baseEnd_5177132] using wordTrace_append hprefix tailTrace_5177132
  have hstable : (prefixWord ++ tailWord_5177132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177132).length < 2 ^ (prefixWord ++ tailWord_5177132).sum := by decide
  have hdescent : baseEnd_5177132 < baseStart_5177132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177160 : List Nat := [2, 1, 3, 1, 1, 6, 2, 1, 1, 3, 2]
def baseStart_5177160 : Nat := 118140960795 + 5177160 * 2 ^ 59
def prefixEnd_5177160 : Nat := 4983230072969 + 3 ^ 40 * 5177160 * 2
def baseEnd_5177160 : Nat := 2658371505231069571390681

theorem tailTrace_5177160 : CollatzResearch.WordTrace tailWord_5177160 prefixEnd_5177160 2658371505231069571390681 := by
  unfold tailWord_5177160
  simp only [CollatzResearch.WordTrace]
  refine ⟨94413268962020491689632467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125884358616027322252843289 94413268962020491689632467)
  ·
    refine ⟨141619903443030737534448701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94413268962020491689632467 141619903443030737534448701)
    ·
      refine ⟨53107463791136526575418263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141619903443030737534448701 53107463791136526575418263)
      ·
        refine ⟨79661195686704789863127395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53107463791136526575418263 79661195686704789863127395)
        ·
          refine ⟨119491793530057184794691093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79661195686704789863127395 119491793530057184794691093)
          ·
            refine ⟨5601177821721430537251145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 119491793530057184794691093 5601177821721430537251145)
            ·
              refine ⟨4200883366291072902938359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5601177821721430537251145 4200883366291072902938359)
              ·
                refine ⟨6301325049436609354407539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4200883366291072902938359 6301325049436609354407539)
                ·
                  refine ⟨9451987574154914031611309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6301325049436609354407539 9451987574154914031611309)
                  ·
                    refine ⟨3544495340308092761854241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9451987574154914031611309 3544495340308092761854241)
                    ·
                      refine ⟨2658371505231069571390681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544495340308092761854241 2658371505231069571390681)
                      ·
                        rfl

theorem cell23_5177160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_5177160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177160 prefixEnd_5177160 := by exact prefixLift 5177160
  have htrace : WordTrace (prefixWord ++ tailWord_5177160) baseStart_5177160 baseEnd_5177160 := by
    simpa [prefixWord, tailWord_5177160, baseEnd_5177160] using wordTrace_append hprefix tailTrace_5177160
  have hstable : (prefixWord ++ tailWord_5177160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177160).length < 2 ^ (prefixWord ++ tailWord_5177160).sum := by decide
  have hdescent : baseEnd_5177160 < baseStart_5177160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177162 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 9]
def baseStart_5177162 : Nat := 118140960795 + 5177162 * 2 ^ 59
def prefixEnd_5177162 : Nat := 4983230072969 + 3 ^ 40 * 5177162 * 2
def baseEnd_5177162 : Nat := 295374725799153173729519

theorem tailTrace_5177162 : CollatzResearch.WordTrace tailWord_5177162 prefixEnd_5177162 295374725799153173729519 := by
  unfold tailWord_5177162
  simp only [CollatzResearch.WordTrace]
  refine ⟨47206652717508434430209435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125884407246689158480558493 47206652717508434430209435)
  ·
    refine ⟨70809979076262651645314153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47206652717508434430209435 70809979076262651645314153)
    ·
      refine ⟨53107484307196988733985615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70809979076262651645314153 53107484307196988733985615)
      ·
        refine ⟨79661226460795483100978423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53107484307196988733985615 79661226460795483100978423)
        ·
          refine ⟨119491839691193224651467635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79661226460795483100978423 119491839691193224651467635)
          ·
            refine ⟨179237759536789836977201453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119491839691193224651467635 179237759536789836977201453)
            ·
              refine ⟨67214159826296188866450545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179237759536789836977201453 67214159826296188866450545)
              ·
                refine ⟨50410619869722141649837909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67214159826296188866450545 50410619869722141649837909)
                ·
                  refine ⟨295374725799153173729519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50410619869722141649837909 295374725799153173729519)
                  ·
                    rfl

theorem cell23_5177162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_5177162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177162 prefixEnd_5177162 := by exact prefixLift 5177162
  have htrace : WordTrace (prefixWord ++ tailWord_5177162) baseStart_5177162 baseEnd_5177162 := by
    simpa [prefixWord, tailWord_5177162, baseEnd_5177162] using wordTrace_append hprefix tailTrace_5177162
  have hstable : (prefixWord ++ tailWord_5177162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177162).length < 2 ^ (prefixWord ++ tailWord_5177162).sum := by decide
  have hdescent : baseEnd_5177162 < baseStart_5177162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177169 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_5177169 : Nat := 118140960795 + 5177169 * 2 ^ 59
def prefixEnd_5177169 : Nat := 4983230072969 + 3 ^ 40 * 5177169 * 2
def baseEnd_5177169 : Nat := 2658376126556960036178139

theorem tailTrace_5177169 : CollatzResearch.WordTrace tailWord_5177169 prefixEnd_5177169 2658376126556960036178139 := by
  unfold tailWord_5177169
  simp only [CollatzResearch.WordTrace]
  refine ⟨188826866181008377916342561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125884577454005585277561707 188826866181008377916342561)
  ·
    refine ⟨141620149635756283437256921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188826866181008377916342561 141620149635756283437256921)
    ·
      refine ⟨106215112226817212577942691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141620149635756283437256921 106215112226817212577942691)
      ·
        refine ⟨159322668340225818866914037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106215112226817212577942691 159322668340225818866914037)
        ·
          refine ⟨14936500156896170518773191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159322668340225818866914037 14936500156896170518773191)
          ·
            refine ⟨22404750235344255778159787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14936500156896170518773191 22404750235344255778159787)
            ·
              refine ⟨33607125353016383667239681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22404750235344255778159787 33607125353016383667239681)
              ·
                refine ⟨25205344014762287750429761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33607125353016383667239681 25205344014762287750429761)
                ·
                  refine ⟨18904008011071715812822321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25205344014762287750429761 18904008011071715812822321)
                  ·
                    refine ⟨14178006008303786859616741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18904008011071715812822321 14178006008303786859616741)
                    ·
                      refine ⟨2658376126556960036178139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14178006008303786859616741 2658376126556960036178139)
                      ·
                        rfl

theorem cell23_5177169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_5177169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177169 prefixEnd_5177169 := by exact prefixLift 5177169
  have htrace : WordTrace (prefixWord ++ tailWord_5177169) baseStart_5177169 baseEnd_5177169 := by
    simpa [prefixWord, tailWord_5177169, baseEnd_5177169] using wordTrace_append hprefix tailTrace_5177169
  have hstable : (prefixWord ++ tailWord_5177169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177169).length < 2 ^ (prefixWord ++ tailWord_5177169).sum := by decide
  have hdescent : baseEnd_5177169 < baseStart_5177169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177173 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_5177173 : Nat := 118140960795 + 5177173 * 2 ^ 59
def prefixEnd_5177173 : Nat := 4983230072969 + 3 ^ 40 * 5177173 * 2
def baseEnd_5177173 : Nat := 2658378180479578020528121

theorem tailTrace_5177173 : CollatzResearch.WordTrace tailWord_5177173 prefixEnd_5177173 2658378180479578020528121 := by
  unfold tailWord_5177173
  simp only [CollatzResearch.WordTrace]
  refine ⟨188827012072993886599488173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125884674715329257732992115 188827012072993886599488173)
  ·
    refine ⟨70810129527372707474808065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188827012072993886599488173 70810129527372707474808065)
    ·
      refine ⟨53107597145529530606106049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70810129527372707474808065 53107597145529530606106049)
      ·
        refine ⟨39830697859147147954579537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53107597145529530606106049 39830697859147147954579537)
        ·
          refine ⟨29873023394360360965934653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39830697859147147954579537 29873023394360360965934653)
          ·
            refine ⟨11202383772885135362225495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29873023394360360965934653 11202383772885135362225495)
            ·
              refine ⟨16803575659327703043338243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11202383772885135362225495 16803575659327703043338243)
              ·
                refine ⟨25205363488991554565007365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16803575659327703043338243 25205363488991554565007365)
                ·
                  refine ⟨4726005654185916480938881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25205363488991554565007365 4726005654185916480938881)
                  ·
                    refine ⟨3544504240639437360704161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4726005654185916480938881 3544504240639437360704161)
                    ·
                      refine ⟨2658378180479578020528121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544504240639437360704161 2658378180479578020528121)
                      ·
                        rfl

theorem cell23_5177173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_5177173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177173 prefixEnd_5177173 := by exact prefixLift 5177173
  have htrace : WordTrace (prefixWord ++ tailWord_5177173) baseStart_5177173 baseEnd_5177173 := by
    simpa [prefixWord, tailWord_5177173, baseEnd_5177173] using wordTrace_append hprefix tailTrace_5177173
  have hstable : (prefixWord ++ tailWord_5177173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177173).length < 2 ^ (prefixWord ++ tailWord_5177173).sum := by decide
  have hdescent : baseEnd_5177173 < baseStart_5177173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177186 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5177186 : Nat := 118140960795 + 5177186 * 2 ^ 59
def prefixEnd_5177186 : Nat := 4983230072969 + 3 ^ 40 * 5177186 * 2
def baseEnd_5177186 : Nat := 2658384855728086469665561

theorem tailTrace_5177186 : CollatzResearch.WordTrace tailWord_5177186 prefixEnd_5177186 2658384855728086469665561 := by
  unfold tailWord_5177186
  simp only [CollatzResearch.WordTrace]
  refine ⟨47206871555486697454927853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125884990814631193213140941 47206871555486697454927853)
  ·
    refine ⟨17702576833307511545597945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47206871555486697454927853 17702576833307511545597945)
    ·
      refine ⟨13276932624980633659198459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17702576833307511545597945 13276932624980633659198459)
      ·
        refine ⟨19915398937470950488797689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13276932624980633659198459 19915398937470950488797689)
        ·
          refine ⟨14936549203103212866598267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19915398937470950488797689 14936549203103212866598267)
          ·
            refine ⟨22404823804654819299897401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14936549203103212866598267 22404823804654819299897401)
            ·
              refine ⟨16803617853491114474923051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22404823804654819299897401 16803617853491114474923051)
              ·
                refine ⟨25205426780236671712384577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16803617853491114474923051 25205426780236671712384577)
                ·
                  refine ⟨18904070085177503784288433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25205426780236671712384577 18904070085177503784288433)
                  ·
                    refine ⟨14178052563883127838216325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18904070085177503784288433 14178052563883127838216325)
                    ·
                      refine ⟨2658384855728086469665561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14178052563883127838216325 2658384855728086469665561)
                      ·
                        rfl

theorem cell23_5177186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5177186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177186 prefixEnd_5177186 := by exact prefixLift 5177186
  have htrace : WordTrace (prefixWord ++ tailWord_5177186) baseStart_5177186 baseEnd_5177186 := by
    simpa [prefixWord, tailWord_5177186, baseEnd_5177186] using wordTrace_append hprefix tailTrace_5177186
  have hstable : (prefixWord ++ tailWord_5177186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177186).length < 2 ^ (prefixWord ++ tailWord_5177186).sum := by decide
  have hdescent : baseEnd_5177186 < baseStart_5177186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177209 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 2, 5]
def baseStart_5177209 : Nat := 118140960795 + 5177209 * 2 ^ 59
def prefixEnd_5177209 : Nat := 4983230072969 + 3 ^ 40 * 5177209 * 2
def baseEnd_5177209 : Nat := 886132221927713293225985

theorem tailTrace_5177209 : CollatzResearch.WordTrace tailWord_5177209 prefixEnd_5177209 886132221927713293225985 := by
  unfold tailWord_5177209
  simp only [CollatzResearch.WordTrace]
  refine ⟨188828325100863464747798681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125885550067242309831865787 188828325100863464747798681)
  ·
    refine ⟨141621243825647598560849011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188828325100863464747798681 141621243825647598560849011)
    ·
      refine ⟨212431865738471397841273517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141621243825647598560849011 212431865738471397841273517)
      ·
        refine ⟨79661949651926774190477569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212431865738471397841273517 79661949651926774190477569)
        ·
          refine ⟨59746462238945080642858177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79661949651926774190477569 59746462238945080642858177)
          ·
            refine ⟨44809846679208810482143633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59746462238945080642858177 44809846679208810482143633)
            ·
              refine ⟨33607385009406607861607725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44809846679208810482143633 33607385009406607861607725)
              ·
                refine ⟨12602769378527477948102897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33607385009406607861607725 12602769378527477948102897)
                ·
                  refine ⟨9452077033895608461077173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12602769378527477948102897 9452077033895608461077173)
                  ·
                    refine ⟨886132221927713293225985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9452077033895608461077173 886132221927713293225985)
                    ·
                      rfl

theorem cell23_5177209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_5177209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177209 prefixEnd_5177209 := by exact prefixLift 5177209
  have htrace : WordTrace (prefixWord ++ tailWord_5177209) baseStart_5177209 baseEnd_5177209 := by
    simpa [prefixWord, tailWord_5177209, baseEnd_5177209] using wordTrace_append hprefix tailTrace_5177209
  have hstable : (prefixWord ++ tailWord_5177209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177209).length < 2 ^ (prefixWord ++ tailWord_5177209).sum := by decide
  have hdescent : baseEnd_5177209 < baseStart_5177209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177230 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_5177230 : Nat := 118140960795 + 5177230 * 2 ^ 59
def prefixEnd_5177230 : Nat := 4983230072969 + 3 ^ 40 * 5177230 * 2
def baseEnd_5177230 : Nat := 295378605430764921946151

theorem tailTrace_5177230 : CollatzResearch.WordTrace tailWord_5177230 prefixEnd_5177230 295378605430764921946151 := by
  unfold tailWord_5177230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23603636379223423166789143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125886060689191590222875429 23603636379223423166789143)
  ·
    refine ⟨35405454568835134750183715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23603636379223423166789143 35405454568835134750183715)
    ·
      refine ⟨53108181853252702125275573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35405454568835134750183715 53108181853252702125275573)
      ·
        refine ⟨4978892048742440824244585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53108181853252702125275573 4978892048742440824244585)
        ·
          refine ⟨3734169036556830618183439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4978892048742440824244585 3734169036556830618183439)
          ·
            refine ⟨5601253554835245927275159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734169036556830618183439 5601253554835245927275159)
            ·
              refine ⟨8401880332252868890912739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601253554835245927275159 8401880332252868890912739)
              ·
                refine ⟨12602820498379303336369109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8401880332252868890912739 12602820498379303336369109)
                ·
                  refine ⟨295378605430764921946151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12602820498379303336369109 295378605430764921946151)
                  ·
                    rfl

theorem cell23_5177230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_5177230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177230 prefixEnd_5177230 := by exact prefixLift 5177230
  have htrace : WordTrace (prefixWord ++ tailWord_5177230) baseStart_5177230 baseEnd_5177230 := by
    simpa [prefixWord, tailWord_5177230, baseEnd_5177230] using wordTrace_append hprefix tailTrace_5177230
  have hstable : (prefixWord ++ tailWord_5177230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177230).length < 2 ^ (prefixWord ++ tailWord_5177230).sum := by decide
  have hdescent : baseEnd_5177230 < baseStart_5177230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177236 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_5177236 : Nat := 118140960795 + 5177236 * 2 ^ 59
def prefixEnd_5177236 : Nat := 4983230072969 + 3 ^ 40 * 5177236 * 2
def baseEnd_5177236 : Nat := 2658410529760811274040331

theorem tailTrace_5177236 : CollatzResearch.WordTrace tailWord_5177236 prefixEnd_5177236 2658410529760811274040331 := by
  unfold tailWord_5177236
  simp only [CollatzResearch.WordTrace]
  refine ⟨94414654935882824179515781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125886206581177098906021041 94414654935882824179515781)
  ·
    refine ⟨17702747800478029533659209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94414654935882824179515781 17702747800478029533659209)
    ·
      refine ⟨13277060850358522150244407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17702747800478029533659209 13277060850358522150244407)
      ·
        refine ⟨19915591275537783225366611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13277060850358522150244407 19915591275537783225366611)
        ·
          refine ⟨29873386913306674838049917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19915591275537783225366611 29873386913306674838049917)
          ·
            refine ⟨11202520092490003064268719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29873386913306674838049917 11202520092490003064268719)
            ·
              refine ⟨16803780138735004596403079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11202520092490003064268719 16803780138735004596403079)
              ·
                refine ⟨25205670208102506894604619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16803780138735004596403079 25205670208102506894604619)
                ·
                  refine ⟨37808505312153760341906929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25205670208102506894604619 37808505312153760341906929)
                  ·
                    refine ⟨28356378984115320256430197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37808505312153760341906929 28356378984115320256430197)
                    ·
                      refine ⟨2658410529760811274040331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28356378984115320256430197 2658410529760811274040331)
                      ·
                        rfl

theorem cell23_5177236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_5177236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177236 prefixEnd_5177236 := by exact prefixLift 5177236
  have htrace : WordTrace (prefixWord ++ tailWord_5177236) baseStart_5177236 baseEnd_5177236 := by
    simpa [prefixWord, tailWord_5177236, baseEnd_5177236] using wordTrace_append hprefix tailTrace_5177236
  have hstable : (prefixWord ++ tailWord_5177236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177236).length < 2 ^ (prefixWord ++ tailWord_5177236).sum := by decide
  have hdescent : baseEnd_5177236 < baseStart_5177236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177273 : List Nat := [1, 2, 1, 4, 2, 1, 2, 5, 1, 4]
def baseStart_5177273 : Nat := 118140960795 + 5177273 * 2 ^ 59
def prefixEnd_5177273 : Nat := 4983230072969 + 3 ^ 40 * 5177273 * 2
def baseEnd_5177273 : Nat := 886143176181675876425887

theorem tailTrace_5177273 : CollatzResearch.WordTrace tailWord_5177273 prefixEnd_5177273 886143176181675876425887 := by
  unfold tailWord_5177273
  simp only [CollatzResearch.WordTrace]
  refine ⟨188830659372631603678128473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125887106248421069118752315 188830659372631603678128473)
  ·
    refine ⟨141622994529473702758596355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188830659372631603678128473 141622994529473702758596355)
    ·
      refine ⟨212434491794210554137894533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141622994529473702758596355 212434491794210554137894533)
      ·
        refine ⟨39831467211414478900855225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212434491794210554137894533 39831467211414478900855225)
        ·
          refine ⟨29873600408560859175641419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39831467211414478900855225 29873600408560859175641419)
          ·
            refine ⟨44810400612841288763462129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29873600408560859175641419 44810400612841288763462129)
            ·
              refine ⟨33607800459630966572596597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44810400612841288763462129 33607800459630966572596597)
              ·
                refine ⟨3150731293090403116180931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33607800459630966572596597 3150731293090403116180931)
                ·
                  refine ⟨4726096939635604674271397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150731293090403116180931 4726096939635604674271397)
                  ·
                    refine ⟨886143176181675876425887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4726096939635604674271397 886143176181675876425887)
                    ·
                      rfl

theorem cell23_5177273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 4].length) (baseStart_5177273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177273 prefixEnd_5177273 := by exact prefixLift 5177273
  have htrace : WordTrace (prefixWord ++ tailWord_5177273) baseStart_5177273 baseEnd_5177273 := by
    simpa [prefixWord, tailWord_5177273, baseEnd_5177273] using wordTrace_append hprefix tailTrace_5177273
  have hstable : (prefixWord ++ tailWord_5177273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177273).length < 2 ^ (prefixWord ++ tailWord_5177273).sum := by decide
  have hdescent : baseEnd_5177273 < baseStart_5177273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177290 : List Nat := [3, 1, 2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_5177290 : Nat := 118140960795 + 5177290 * 2 ^ 59
def prefixEnd_5177290 : Nat := 4983230072969 + 3 ^ 40 * 5177290 * 2
def baseEnd_5177290 : Nat := 886146085905384687588361

theorem tailTrace_5177290 : CollatzResearch.WordTrace tailWord_5177290 prefixEnd_5177290 886146085905384687588361 := by
  unfold tailWord_5177290
  simp only [CollatzResearch.WordTrace]
  refine ⟨47207819853392503895374331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125887519609046677054331549 47207819853392503895374331)
  ·
    refine ⟨70811729780088755843061497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47207819853392503895374331 70811729780088755843061497)
    ·
      refine ⟨53108797335066566882296123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70811729780088755843061497 53108797335066566882296123)
      ·
        refine ⟨79663196002599850323444185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53108797335066566882296123 79663196002599850323444185)
        ·
          refine ⟨59747397001949887742583139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79663196002599850323444185 59747397001949887742583139)
          ·
            refine ⟨89621095502924831613874709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59747397001949887742583139 89621095502924831613874709)
            ·
              refine ⟨4200988851699601481900377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89621095502924831613874709 4200988851699601481900377)
              ·
                refine ⟨3150741638774701111425283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4200988851699601481900377 3150741638774701111425283)
                ·
                  refine ⟨4726112458162051667137925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150741638774701111425283 4726112458162051667137925)
                  ·
                    refine ⟨886146085905384687588361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4726112458162051667137925 886146085905384687588361)
                    ·
                      rfl

theorem cell23_5177290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_5177290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177290 prefixEnd_5177290 := by exact prefixLift 5177290
  have htrace : WordTrace (prefixWord ++ tailWord_5177290) baseStart_5177290 baseEnd_5177290 := by
    simpa [prefixWord, tailWord_5177290, baseEnd_5177290] using wordTrace_append hprefix tailTrace_5177290
  have hstable : (prefixWord ++ tailWord_5177290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177290).length < 2 ^ (prefixWord ++ tailWord_5177290).sum := by decide
  have hdescent : baseEnd_5177290 < baseStart_5177290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177316 : List Nat := [2, 3, 1, 1, 1, 1, 4, 4, 1, 5]
def baseStart_5177316 : Nat := 118140960795 + 5177316 * 2 ^ 59
def prefixEnd_5177316 : Nat := 4983230072969 + 3 ^ 40 * 5177316 * 2
def baseEnd_5177316 : Nat := 886150536071056987013321

theorem tailTrace_5177316 : CollatzResearch.WordTrace tailWord_5177316 prefixEnd_5177316 886150536071056987013321 := by
  unfold tailWord_5177316
  simp only [CollatzResearch.WordTrace]
  refine ⟨94416113855737911010971901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125888151807650548014629201 94416113855737911010971901)
  ·
    refine ⟨35406042695901716629114463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94416113855737911010971901 35406042695901716629114463)
    ·
      refine ⟨53109064043852574943671695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35406042695901716629114463 53109064043852574943671695)
      ·
        refine ⟨79663596065778862415507543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53109064043852574943671695 79663596065778862415507543)
        ·
          refine ⟨119495394098668293623261315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79663596065778862415507543 119495394098668293623261315)
          ·
            refine ⟨179243091148002440434891973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119495394098668293623261315 179243091148002440434891973)
            ·
              refine ⟨33608079590250457581542245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179243091148002440434891973 33608079590250457581542245)
              ·
                refine ⟨6301514923171960796539171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33608079590250457581542245 6301514923171960796539171)
                ·
                  refine ⟨9452272384757941194808757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6301514923171960796539171 9452272384757941194808757)
                  ·
                    refine ⟨886150536071056987013321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9452272384757941194808757 886150536071056987013321)
                    ·
                      rfl

theorem cell23_5177316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_5177316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177316 prefixEnd_5177316 := by exact prefixLift 5177316
  have htrace : WordTrace (prefixWord ++ tailWord_5177316) baseStart_5177316 baseEnd_5177316 := by
    simpa [prefixWord, tailWord_5177316, baseEnd_5177316] using wordTrace_append hprefix tailTrace_5177316
  have hstable : (prefixWord ++ tailWord_5177316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177316).length < 2 ^ (prefixWord ++ tailWord_5177316).sum := by decide
  have hdescent : baseEnd_5177316 < baseStart_5177316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177356 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 1, 1, 5]
def baseStart_5177356 : Nat := 118140960795 + 5177356 * 2 ^ 59
def prefixEnd_5177356 : Nat := 4983230072969 + 3 ^ 40 * 5177356 * 2
def baseEnd_5177356 : Nat := 2658472147439350804539779

theorem tailTrace_5177356 : CollatzResearch.WordTrace tailWord_5177356 prefixEnd_5177356 2658472147439350804539779 := by
  unfold tailWord_5177356
  simp only [CollatzResearch.WordTrace]
  refine ⟨94416843315665454426699961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125889124420887272568933281 94416843315665454426699961)
  ·
    refine ⟨70812632486749090820024971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94416843315665454426699961 70812632486749090820024971)
    ·
      refine ⟨106218948730123636230037457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70812632486749090820024971 106218948730123636230037457)
      ·
        refine ⟨79664211547592727172528093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106218948730123636230037457 79664211547592727172528093)
        ·
          refine ⟨29874079330347272689698035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79664211547592727172528093 29874079330347272689698035)
          ·
            refine ⟨44811118995520909034547053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29874079330347272689698035 44811118995520909034547053)
            ·
              refine ⟨16804169623320340887955145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44811118995520909034547053 16804169623320340887955145)
              ·
                refine ⟨12603127217490255665966359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16804169623320340887955145 12603127217490255665966359)
                ·
                  refine ⟨18904690826235383498949539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12603127217490255665966359 18904690826235383498949539)
                  ·
                    refine ⟨28357036239353075248424309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18904690826235383498949539 28357036239353075248424309)
                    ·
                      refine ⟨2658472147439350804539779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28357036239353075248424309 2658472147439350804539779)
                      ·
                        rfl

theorem cell23_5177356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_5177356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177356 prefixEnd_5177356 := by exact prefixLift 5177356
  have htrace : WordTrace (prefixWord ++ tailWord_5177356) baseStart_5177356 baseEnd_5177356 := by
    simpa [prefixWord, tailWord_5177356, baseEnd_5177356] using wordTrace_append hprefix tailTrace_5177356
  have hstable : (prefixWord ++ tailWord_5177356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177356).length < 2 ^ (prefixWord ++ tailWord_5177356).sum := by decide
  have hdescent : baseEnd_5177356 < baseStart_5177356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177370 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2]
def baseStart_5177370 : Nat := 118140960795 + 5177370 * 2 ^ 59
def prefixEnd_5177370 : Nat := 4983230072969 + 3 ^ 40 * 5177370 * 2
def baseEnd_5177370 : Nat := 2658479336168513749764715

theorem tailTrace_5177370 : CollatzResearch.WordTrace tailWord_5177370 prefixEnd_5177370 2658479336168513749764715 := by
  unfold tailWord_5177370
  simp only [CollatzResearch.WordTrace]
  refine ⟨47208549313320047311102391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125889464835520126162939709 47208549313320047311102391)
  ·
    refine ⟨70812823969980070966653587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47208549313320047311102391 70812823969980070966653587)
    ·
      refine ⟨106219235954970106449980381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70812823969980070966653587 106219235954970106449980381)
      ·
        refine ⟨39832213483113789918742643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106219235954970106449980381 39832213483113789918742643)
        ·
          refine ⟨59748320224670684878113965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39832213483113789918742643 59748320224670684878113965)
          ·
            refine ⟨22405620084251506829292737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59748320224670684878113965 22405620084251506829292737)
            ·
              refine ⟨16804215063188630121969553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22405620084251506829292737 16804215063188630121969553)
              ·
                refine ⟨12603161297391472591477165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16804215063188630121969553 12603161297391472591477165)
                ·
                  refine ⟨4726185486521802221803937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12603161297391472591477165 4726185486521802221803937)
                  ·
                    refine ⟨3544639114891351666352953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4726185486521802221803937 3544639114891351666352953)
                    ·
                      refine ⟨2658479336168513749764715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544639114891351666352953 2658479336168513749764715)
                      ·
                        rfl

theorem cell23_5177370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_5177370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177370 prefixEnd_5177370 := by exact prefixLift 5177370
  have htrace : WordTrace (prefixWord ++ tailWord_5177370) baseStart_5177370 baseEnd_5177370 := by
    simpa [prefixWord, tailWord_5177370, baseEnd_5177370] using wordTrace_append hprefix tailTrace_5177370
  have hstable : (prefixWord ++ tailWord_5177370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177370).length < 2 ^ (prefixWord ++ tailWord_5177370).sum := by decide
  have hdescent : baseEnd_5177370 < baseStart_5177370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177390 : List Nat := [4, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_5177390 : Nat := 118140960795 + 5177390 * 2 ^ 59
def prefixEnd_5177390 : Nat := 4983230072969 + 3 ^ 40 * 5177390 * 2
def baseEnd_5177390 : Nat := 2658489605781603671514623

theorem tailTrace_5177390 : CollatzResearch.WordTrace tailWord_5177390 prefixEnd_5177390 2658489605781603671514623 := by
  unfold tailWord_5177390
  simp only [CollatzResearch.WordTrace]
  refine ⟨23604365839150966582517203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125889951142138488440091749 23604365839150966582517203)
  ·
    refine ⟨35406548758726449873775805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23604365839150966582517203 35406548758726449873775805)
    ·
      refine ⟨13277455784522418702665927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35406548758726449873775805 13277455784522418702665927)
      ·
        refine ⟨19916183676783628053998891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13277455784522418702665927 19916183676783628053998891)
        ·
          refine ⟨29874275515175442080998337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19916183676783628053998891 29874275515175442080998337)
          ·
            refine ⟨22405706636381581560748753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29874275515175442080998337 22405706636381581560748753)
            ·
              refine ⟨16804279977286186170561565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22405706636381581560748753 16804279977286186170561565)
              ·
                refine ⟨6301604991482319813960587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16804279977286186170561565 6301604991482319813960587)
                ·
                  refine ⟨9452407487223479720940881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6301604991482319813960587 9452407487223479720940881)
                  ·
                    refine ⟨7089305615417609790705661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9452407487223479720940881 7089305615417609790705661)
                    ·
                      refine ⟨2658489605781603671514623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7089305615417609790705661 2658489605781603671514623)
                      ·
                        rfl

theorem cell23_5177390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_5177390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177390 prefixEnd_5177390 := by exact prefixLift 5177390
  have htrace : WordTrace (prefixWord ++ tailWord_5177390) baseStart_5177390 baseEnd_5177390 := by
    simpa [prefixWord, tailWord_5177390, baseEnd_5177390] using wordTrace_append hprefix tailTrace_5177390
  have hstable : (prefixWord ++ tailWord_5177390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177390).length < 2 ^ (prefixWord ++ tailWord_5177390).sum := by decide
  have hdescent : baseEnd_5177390 < baseStart_5177390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177404 : List Nat := [2, 2, 2, 2, 2, 1, 5, 2, 1, 2, 2]
def baseStart_5177404 : Nat := 118140960795 + 5177404 * 2 ^ 59
def prefixEnd_5177404 : Nat := 4983230072969 + 3 ^ 40 * 5177404 * 2
def baseEnd_5177404 : Nat := 2658496794510766616739559

theorem tailTrace_5177404 : CollatzResearch.WordTrace tailWord_5177404 prefixEnd_5177404 2658496794510766616739559 := by
  unfold tailWord_5177404
  simp only [CollatzResearch.WordTrace]
  refine ⟨94417718667578506525573633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125890291556771342034098177 94417718667578506525573633)
  ·
    refine ⟨70813289000683879894180225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94417718667578506525573633 70813289000683879894180225)
    ·
      refine ⟨53109966750512909920635169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70813289000683879894180225 53109966750512909920635169)
      ·
        refine ⟨39832475062884682440476377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53109966750512909920635169 39832475062884682440476377)
        ·
          refine ⟨29874356297163511830357283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39832475062884682440476377 29874356297163511830357283)
          ·
            refine ⟨44811534445745267745535925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29874356297163511830357283 44811534445745267745535925)
            ·
              refine ⟨4201081354288618851143993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44811534445745267745535925 4201081354288618851143993)
              ·
                refine ⟨3150811015716464138357995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4201081354288618851143993 3150811015716464138357995)
                ·
                  refine ⟨4726216523574696207536993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150811015716464138357995 4726216523574696207536993)
                  ·
                    refine ⟨3544662392681022155652745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4726216523574696207536993 3544662392681022155652745)
                    ·
                      refine ⟨2658496794510766616739559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544662392681022155652745 2658496794510766616739559)
                      ·
                        rfl

theorem cell23_5177404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_5177404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177404 prefixEnd_5177404 := by exact prefixLift 5177404
  have htrace : WordTrace (prefixWord ++ tailWord_5177404) baseStart_5177404 baseEnd_5177404 := by
    simpa [prefixWord, tailWord_5177404, baseEnd_5177404] using wordTrace_append hprefix tailTrace_5177404
  have hstable : (prefixWord ++ tailWord_5177404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177404).length < 2 ^ (prefixWord ++ tailWord_5177404).sum := by decide
  have hdescent : baseEnd_5177404 < baseStart_5177404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177413 : List Nat := [1, 3, 1, 1, 1, 3, 1, 4, 3, 3, 2]
def baseStart_5177413 : Nat := 118140960795 + 5177413 * 2 ^ 59
def prefixEnd_5177413 : Nat := 4983230072969 + 3 ^ 40 * 5177413 * 2
def baseEnd_5177413 : Nat := 2658501415836657081527017

theorem tailTrace_5177413 : CollatzResearch.WordTrace tailWord_5177413 prefixEnd_5177413 2658501415836657081527017 := by
  unfold tailWord_5177413
  simp only [CollatzResearch.WordTrace]
  refine ⟨188835765592124407588224893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125890510394749605058816595 188835765592124407588224893)
  ·
    refine ⟨70813412097046652845584335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188835765592124407588224893 70813412097046652845584335)
    ·
      refine ⟨106220118145569979268376503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70813412097046652845584335 106220118145569979268376503)
      ·
        refine ⟨159330177218354968902564755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106220118145569979268376503 159330177218354968902564755)
        ·
          refine ⟨238995265827532453353847133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159330177218354968902564755 238995265827532453353847133)
          ·
            refine ⟨89623224685324670007692675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238995265827532453353847133 89623224685324670007692675)
            ·
              refine ⟨134434837027987005011539013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89623224685324670007692675 134434837027987005011539013)
              ·
                refine ⟨25206531942747563439663565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134434837027987005011539013 25206531942747563439663565)
                ·
                  refine ⟨9452449478530336289873837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25206531942747563439663565 9452449478530336289873837)
                  ·
                    refine ⟨3544668554448876108702689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9452449478530336289873837 3544668554448876108702689)
                    ·
                      refine ⟨2658501415836657081527017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544668554448876108702689 2658501415836657081527017)
                      ·
                        rfl

theorem cell23_5177413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_5177413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177413 prefixEnd_5177413 := by exact prefixLift 5177413
  have htrace : WordTrace (prefixWord ++ tailWord_5177413) baseStart_5177413 baseEnd_5177413 := by
    simpa [prefixWord, tailWord_5177413, baseEnd_5177413] using wordTrace_append hprefix tailTrace_5177413
  have hstable : (prefixWord ++ tailWord_5177413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177413).length < 2 ^ (prefixWord ++ tailWord_5177413).sum := by decide
  have hdescent : baseEnd_5177413 < baseStart_5177413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177443 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 3, 4, 2]
def baseStart_5177443 : Nat := 118140960795 + 5177443 * 2 ^ 59
def prefixEnd_5177443 : Nat := 4983230072969 + 3 ^ 40 * 5177443 * 2
def baseEnd_5177443 : Nat := 2658516820256291964151879

theorem tailTrace_5177443 : CollatzResearch.WordTrace tailWord_5177443 prefixEnd_5177443 2658516820256291964151879 := by
  unfold tailWord_5177443
  simp only [CollatzResearch.WordTrace]
  refine ⟨188836859782015722711816983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125891239854677148474544655 188836859782015722711816983)
  ·
    refine ⟨283255289673023584067725475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188836859782015722711816983 283255289673023584067725475)
    ·
      refine ⟨424882934509535376101588213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283255289673023584067725475 424882934509535376101588213)
      ·
        refine ⟨39832775110268941509523895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 424882934509535376101588213 39832775110268941509523895)
        ·
          refine ⟨59749162665403412264285843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39832775110268941509523895 59749162665403412264285843)
          ·
            refine ⟨89623743998105118396428765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59749162665403412264285843 89623743998105118396428765)
            ·
              refine ⟨33608903999289419398660787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89623743998105118396428765 33608903999289419398660787)
              ·
                refine ⟨50413355998934129097991181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33608903999289419398660787 50413355998934129097991181)
                ·
                  refine ⟨18905008499600298411746693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50413355998934129097991181 18905008499600298411746693)
                  ·
                    refine ⟨3544689093675055952202505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18905008499600298411746693 3544689093675055952202505)
                    ·
                      refine ⟨2658516820256291964151879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544689093675055952202505 2658516820256291964151879)
                      ·
                        rfl

theorem cell23_5177443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_5177443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177443 prefixEnd_5177443 := by exact prefixLift 5177443
  have htrace : WordTrace (prefixWord ++ tailWord_5177443) baseStart_5177443 baseEnd_5177443 := by
    simpa [prefixWord, tailWord_5177443, baseEnd_5177443] using wordTrace_append hprefix tailTrace_5177443
  have hstable : (prefixWord ++ tailWord_5177443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177443).length < 2 ^ (prefixWord ++ tailWord_5177443).sum := by decide
  have hdescent : baseEnd_5177443 < baseStart_5177443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177447 : List Nat := [1, 1, 5, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_5177447 : Nat := 118140960795 + 5177447 * 2 ^ 59
def prefixEnd_5177447 : Nat := 4983230072969 + 3 ^ 40 * 5177447 * 2
def baseEnd_5177447 : Nat := 2658518874178909948501861

theorem tailTrace_5177447 : CollatzResearch.WordTrace tailWord_5177447 prefixEnd_5177447 2658518874178909948501861 := by
  unfold tailWord_5177447
  simp only [CollatzResearch.WordTrace]
  refine ⟨188837005674001231394962595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125891337116000820929975063 188837005674001231394962595)
  ·
    refine ⟨283255508511001847092443893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188837005674001231394962595 283255508511001847092443893)
    ·
      refine ⟨26555203922906423164916615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 283255508511001847092443893 26555203922906423164916615)
      ·
        refine ⟨39832805884359634747374923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26555203922906423164916615 39832805884359634747374923)
        ·
          refine ⟨59749208826539452121062385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39832805884359634747374923 59749208826539452121062385)
          ·
            refine ⟨44811906619904589090796789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59749208826539452121062385 44811906619904589090796789)
            ·
              refine ⟨4201116245616055227262199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44811906619904589090796789 4201116245616055227262199)
              ·
                refine ⟨6301674368424082840893299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201116245616055227262199 6301674368424082840893299)
                ·
                  refine ⟨9452511552636124261339949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6301674368424082840893299 9452511552636124261339949)
                  ·
                    refine ⟨3544691832238546598002481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9452511552636124261339949 3544691832238546598002481)
                    ·
                      refine ⟨2658518874178909948501861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544691832238546598002481 2658518874178909948501861)
                      ·
                        rfl

theorem cell23_5177447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_5177447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177447 prefixEnd_5177447 := by exact prefixLift 5177447
  have htrace : WordTrace (prefixWord ++ tailWord_5177447) baseStart_5177447 baseEnd_5177447 := by
    simpa [prefixWord, tailWord_5177447, baseEnd_5177447] using wordTrace_append hprefix tailTrace_5177447
  have hstable : (prefixWord ++ tailWord_5177447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177447).length < 2 ^ (prefixWord ++ tailWord_5177447).sum := by decide
  have hdescent : baseEnd_5177447 < baseStart_5177447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177477 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 2, 2, 2]
def baseStart_5177477 : Nat := 118140960795 + 5177477 * 2 ^ 59
def prefixEnd_5177477 : Nat := 4983230072969 + 3 ^ 40 * 5177477 * 2
def baseEnd_5177477 : Nat := 2658534278598544831126723

theorem tailTrace_5177477 : CollatzResearch.WordTrace tailWord_5177477 prefixEnd_5177477 2658534278598544831126723 := by
  unfold tailWord_5177477
  simp only [CollatzResearch.WordTrace]
  refine ⟨188838099863892546518554685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125892066575928364345703123 188838099863892546518554685)
  ·
    refine ⟨70814287448959704944458007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188838099863892546518554685 70814287448959704944458007)
    ·
      refine ⟨106221431173439557416687011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70814287448959704944458007 106221431173439557416687011)
      ·
        refine ⟨159332146760159336125030517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106221431173439557416687011 159332146760159336125030517)
        ·
          refine ⟨14937388758764937761721611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159332146760159336125030517 14937388758764937761721611)
          ·
            refine ⟨22406083138147406642582417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14937388758764937761721611 22406083138147406642582417)
            ·
              refine ⟨16804562353610554981936813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22406083138147406642582417 16804562353610554981936813)
              ·
                refine ⟨6301710882603958118226305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16804562353610554981936813 6301710882603958118226305)
                ·
                  refine ⟨4726283161952968588669729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6301710882603958118226305 4726283161952968588669729)
                  ·
                    refine ⟨3544712371464726441502297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4726283161952968588669729 3544712371464726441502297)
                    ·
                      refine ⟨2658534278598544831126723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544712371464726441502297 2658534278598544831126723)
                      ·
                        rfl

theorem cell23_5177477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_5177477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177477 prefixEnd_5177477 := by exact prefixLift 5177477
  have htrace : WordTrace (prefixWord ++ tailWord_5177477) baseStart_5177477 baseEnd_5177477 := by
    simpa [prefixWord, tailWord_5177477, baseEnd_5177477] using wordTrace_append hprefix tailTrace_5177477
  have hstable : (prefixWord ++ tailWord_5177477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177477).length < 2 ^ (prefixWord ++ tailWord_5177477).sum := by decide
  have hdescent : baseEnd_5177477 < baseStart_5177477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177500 : List Nat := [2, 2, 3, 2, 1, 1, 4, 3, 5]
def baseStart_5177500 : Nat := 118140960795 + 5177500 * 2 ^ 59
def prefixEnd_5177500 : Nat := 4983230072969 + 3 ^ 40 * 5177500 * 2
def baseEnd_5177500 : Nat := 295394009850399804571013

theorem tailTrace_5177500 : CollatzResearch.WordTrace tailWord_5177500 prefixEnd_5177500 295394009850399804571013 := by
  unfold tailWord_5177500
  simp only [CollatzResearch.WordTrace]
  refine ⟨94419469371404610723320977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125892625828539480964427969 94419469371404610723320977)
  ·
    refine ⟨70814602028553458042490733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94419469371404610723320977 70814602028553458042490733)
    ·
      refine ⟨26555475760707546765934025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70814602028553458042490733 26555475760707546765934025)
      ·
        refine ⟨19916606820530660074450519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26555475760707546765934025 19916606820530660074450519)
        ·
          refine ⟨29874910230795990111675779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19916606820530660074450519 29874910230795990111675779)
          ·
            refine ⟨44812365346193985167513669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29874910230795990111675779 44812365346193985167513669)
            ·
              refine ⟨8402318502411372218908813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44812365346193985167513669 8402318502411372218908813)
              ·
                refine ⟨3150869438404264582090805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8402318502411372218908813 3150869438404264582090805)
                ·
                  refine ⟨295394009850399804571013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3150869438404264582090805 295394009850399804571013)
                  ·
                    rfl

theorem cell23_5177500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_5177500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177500 prefixEnd_5177500 := by exact prefixLift 5177500
  have htrace : WordTrace (prefixWord ++ tailWord_5177500) baseStart_5177500 baseEnd_5177500 := by
    simpa [prefixWord, tailWord_5177500, baseEnd_5177500] using wordTrace_append hprefix tailTrace_5177500
  have hstable : (prefixWord ++ tailWord_5177500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177500).length < 2 ^ (prefixWord ++ tailWord_5177500).sum := by decide
  have hdescent : baseEnd_5177500 < baseStart_5177500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177511 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_5177511 : Nat := 118140960795 + 5177511 * 2 ^ 59
def prefixEnd_5177511 : Nat := 4983230072969 + 3 ^ 40 * 5177511 * 2
def baseEnd_5177511 : Nat := 2658551736940797698101567

theorem tailTrace_5177511 : CollatzResearch.WordTrace tailWord_5177511 prefixEnd_5177511 2658551736940797698101567 := by
  unfold tailWord_5177511
  simp only [CollatzResearch.WordTrace]
  refine ⟨188839339945769370325292387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125892893297179580216861591 188839339945769370325292387)
  ·
    refine ⟨283259009918654055487938581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188839339945769370325292387 283259009918654055487938581)
    ·
      refine ⟨13277766089936908850997121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 283259009918654055487938581 13277766089936908850997121)
      ·
        refine ⟨9958324567452681638247841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13277766089936908850997121 9958324567452681638247841)
        ·
          refine ⟨7468743425589511228685881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9958324567452681638247841 7468743425589511228685881)
          ·
            refine ⟨5601557569192133421514411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7468743425589511228685881 5601557569192133421514411)
            ·
              refine ⟨8402336353788200132271617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601557569192133421514411 8402336353788200132271617)
              ·
                refine ⟨6301752265341150099203713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8402336353788200132271617 6301752265341150099203713)
                ·
                  refine ⟨4726314199005862574402785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6301752265341150099203713 4726314199005862574402785)
                  ·
                    refine ⟨3544735649254396930802089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4726314199005862574402785 3544735649254396930802089)
                    ·
                      refine ⟨2658551736940797698101567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544735649254396930802089 2658551736940797698101567)
                      ·
                        rfl

theorem cell23_5177511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_5177511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177511 prefixEnd_5177511 := by exact prefixLift 5177511
  have htrace : WordTrace (prefixWord ++ tailWord_5177511) baseStart_5177511 baseEnd_5177511 := by
    simpa [prefixWord, tailWord_5177511, baseEnd_5177511] using wordTrace_append hprefix tailTrace_5177511
  have hstable : (prefixWord ++ tailWord_5177511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177511).length < 2 ^ (prefixWord ++ tailWord_5177511).sum := by decide
  have hdescent : baseEnd_5177511 < baseStart_5177511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177553 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 3]
def baseStart_5177553 : Nat := 118140960795 + 5177553 * 2 ^ 59
def prefixEnd_5177553 : Nat := 4983230072969 + 3 ^ 40 * 5177553 * 2
def baseEnd_5177553 : Nat := 2658573303128286533776373

theorem tailTrace_5177553 : CollatzResearch.WordTrace tailWord_5177553 prefixEnd_5177553 2658573303128286533776373 := by
  unfold tailWord_5177553
  simp only [CollatzResearch.WordTrace]
  refine ⟨188840871811617211498321313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125893914541078140998880875 188840871811617211498321313)
  ·
    refine ⟨141630653858712908623740985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188840871811617211498321313 141630653858712908623740985)
    ·
      refine ⟨106222990394034681467805739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141630653858712908623740985 106222990394034681467805739)
      ·
        refine ⟨159334485591052022201708609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106222990394034681467805739 159334485591052022201708609)
        ·
          refine ⟨119500864193289016651281457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159334485591052022201708609 119500864193289016651281457)
          ·
            refine ⟨89625648144966762488461093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119500864193289016651281457 89625648144966762488461093)
            ·
              refine ⟨16804809027181267966586455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89625648144966762488461093 16804809027181267966586455)
              ·
                refine ⟨25207213540771901949879683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16804809027181267966586455 25207213540771901949879683)
                ·
                  refine ⟨37810820311157852924819525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25207213540771901949879683 37810820311157852924819525)
                  ·
                    refine ⟨7089528808342097423403661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37810820311157852924819525 7089528808342097423403661)
                    ·
                      refine ⟨2658573303128286533776373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7089528808342097423403661 2658573303128286533776373)
                      ·
                        rfl

theorem cell23_5177553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_5177553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177553 prefixEnd_5177553 := by exact prefixLift 5177553
  have htrace : WordTrace (prefixWord ++ tailWord_5177553) baseStart_5177553 baseEnd_5177553 := by
    simpa [prefixWord, tailWord_5177553, baseEnd_5177553] using wordTrace_append hprefix tailTrace_5177553
  have hstable : (prefixWord ++ tailWord_5177553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177553).length < 2 ^ (prefixWord ++ tailWord_5177553).sum := by decide
  have hdescent : baseEnd_5177553 < baseStart_5177553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177573 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 8]
def baseStart_5177573 : Nat := 118140960795 + 5177573 * 2 ^ 59
def prefixEnd_5177573 : Nat := 4983230072969 + 3 ^ 40 * 5177573 * 2
def baseEnd_5177573 : Nat := 295398174749041828391809

theorem tailTrace_5177573 : CollatzResearch.WordTrace tailWord_5177573 prefixEnd_5177573 295398174749041828391809 := by
  unfold tailWord_5177573
  simp only [CollatzResearch.WordTrace]
  refine ⟨188841601271544754914049373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125894400847696503276032915 188841601271544754914049373)
  ·
    refine ⟨70815600476829283092768515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188841601271544754914049373 70815600476829283092768515)
    ·
      refine ⟨106223400715243924639152773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70815600476829283092768515 106223400715243924639152773)
      ·
        refine ⟨19916887634108235869841145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106223400715243924639152773 19916887634108235869841145)
        ·
          refine ⟨14937665725581176902380859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19916887634108235869841145 14937665725581176902380859)
          ·
            refine ⟨22406498588371765353571289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14937665725581176902380859 22406498588371765353571289)
            ·
              refine ⟨16804873941278824015178467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22406498588371765353571289 16804873941278824015178467)
              ·
                refine ⟨25207310911918236022767701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16804873941278824015178467 25207310911918236022767701)
                ·
                  refine ⟨295398174749041828391809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25207310911918236022767701 295398174749041828391809)
                  ·
                    rfl

theorem cell23_5177573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 8].length) (baseStart_5177573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177573 prefixEnd_5177573 := by exact prefixLift 5177573
  have htrace : WordTrace (prefixWord ++ tailWord_5177573) baseStart_5177573 baseEnd_5177573 := by
    simpa [prefixWord, tailWord_5177573, baseEnd_5177573] using wordTrace_append hprefix tailTrace_5177573
  have hstable : (prefixWord ++ tailWord_5177573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177573).length < 2 ^ (prefixWord ++ tailWord_5177573).sum := by decide
  have hdescent : baseEnd_5177573 < baseStart_5177573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177600 : List Nat := [2, 1, 1, 2, 1, 1, 4, 4, 3, 1, 3]
def baseStart_5177600 : Nat := 118140960795 + 5177600 * 2 ^ 59
def prefixEnd_5177600 : Nat := 4983230072969 + 3 ^ 40 * 5177600 * 2
def baseEnd_5177600 : Nat := 2658597436719047849888657

theorem tailTrace_5177600 : CollatzResearch.WordTrace tailWord_5177600 prefixEnd_5177600 2658597436719047849888657 := by
  unfold tailWord_5177600
  simp only [CollatzResearch.WordTrace]
  refine ⟨94421293021223469262641127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125895057361631292350188169 94421293021223469262641127)
  ·
    refine ⟨141631939531835203893961691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94421293021223469262641127 141631939531835203893961691)
    ·
      refine ⟨212447909297752805840942537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141631939531835203893961691 212447909297752805840942537)
      ·
        refine ⟨159335931973314604380706903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212447909297752805840942537 159335931973314604380706903)
        ·
          refine ⟨239003897959971906571060355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159335931973314604380706903 239003897959971906571060355)
          ·
            refine ⟨358505846939957859856590533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239003897959971906571060355 358505846939957859856590533)
            ·
              refine ⟨67219846301242098723110725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 358505846939957859856590533 67219846301242098723110725)
              ·
                refine ⟨12603721181482893510583261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67219846301242098723110725 12603721181482893510583261)
                ·
                  refine ⟨4726395443056085066468723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12603721181482893510583261 4726395443056085066468723)
                  ·
                    refine ⟨7089593164584127599703085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4726395443056085066468723 7089593164584127599703085)
                    ·
                      refine ⟨2658597436719047849888657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7089593164584127599703085 2658597436719047849888657)
                      ·
                        rfl

theorem cell23_5177600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_5177600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177600 prefixEnd_5177600 := by exact prefixLift 5177600
  have htrace : WordTrace (prefixWord ++ tailWord_5177600) baseStart_5177600 baseEnd_5177600 := by
    simpa [prefixWord, tailWord_5177600, baseEnd_5177600] using wordTrace_append hprefix tailTrace_5177600
  have hstable : (prefixWord ++ tailWord_5177600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177600).length < 2 ^ (prefixWord ++ tailWord_5177600).sum := by decide
  have hdescent : baseEnd_5177600 < baseStart_5177600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177603 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 3, 5]
def baseStart_5177603 : Nat := 118140960795 + 5177603 * 2 ^ 59
def prefixEnd_5177603 : Nat := 4983230072969 + 3 ^ 40 * 5177603 * 2
def baseEnd_5177603 : Nat := 886199659053670446050381

theorem tailTrace_5177603 : CollatzResearch.WordTrace tailWord_5177603 prefixEnd_5177603 886199659053670446050381 := by
  unfold tailWord_5177603
  simp only [CollatzResearch.WordTrace]
  refine ⟨188842695461436070037641463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125895130307624046691760975 188842695461436070037641463)
  ·
    refine ⟨283264043192154105056462195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188842695461436070037641463 283264043192154105056462195)
    ·
      refine ⟨424896064788231157584693293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283264043192154105056462195 424896064788231157584693293)
      ·
        refine ⟨159336024295586684094259985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424896064788231157584693293 159336024295586684094259985)
        ·
          refine ⟨119502018221690013070694989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159336024295586684094259985 119502018221690013070694989)
          ·
            refine ⟨44813256833133754901510621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119502018221690013070694989 44813256833133754901510621)
            ·
              refine ⟨16804971312425158088066483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44813256833133754901510621 16804971312425158088066483)
              ·
                refine ⟨25207456968637737132099725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16804971312425158088066483 25207456968637737132099725)
                ·
                  refine ⟨9452796363239151424537397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25207456968637737132099725 9452796363239151424537397)
                  ·
                    refine ⟨886199659053670446050381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9452796363239151424537397 886199659053670446050381)
                    ·
                      rfl

theorem cell23_5177603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 5].length) (baseStart_5177603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177603 prefixEnd_5177603 := by exact prefixLift 5177603
  have htrace : WordTrace (prefixWord ++ tailWord_5177603) baseStart_5177603 baseEnd_5177603 := by
    simpa [prefixWord, tailWord_5177603, baseEnd_5177603] using wordTrace_append hprefix tailTrace_5177603
  have hstable : (prefixWord ++ tailWord_5177603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177603).length < 2 ^ (prefixWord ++ tailWord_5177603).sum := by decide
  have hdescent : baseEnd_5177603 < baseStart_5177603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177610 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_5177610 : Nat := 118140960795 + 5177610 * 2 ^ 59
def prefixEnd_5177610 : Nat := 4983230072969 + 3 ^ 40 * 5177610 * 2
def baseEnd_5177610 : Nat := 2658602571525592810763611

theorem tailTrace_5177610 : CollatzResearch.WordTrace tailWord_5177610 prefixEnd_5177610 2658602571525592810763611 := by
  unfold tailWord_5177610
  simp only [CollatzResearch.WordTrace]
  refine ⟨47210737693102677558286571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125895300514940473488764189 47210737693102677558286571)
  ·
    refine ⟨70816106539654016337429857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47210737693102677558286571 70816106539654016337429857)
    ·
      refine ⟨53112079904740512253072393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70816106539654016337429857 53112079904740512253072393)
      ·
        refine ⟨39834059928555384189804295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53112079904740512253072393 39834059928555384189804295)
        ·
          refine ⟨59751089892833076284706443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39834059928555384189804295 59751089892833076284706443)
          ·
            refine ⟨89626634839249614427059665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59751089892833076284706443 89626634839249614427059665)
            ·
              refine ⟨67219976129437210820294749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89626634839249614427059665 67219976129437210820294749)
              ·
                refine ⟨25207491048538954057610531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67219976129437210820294749 25207491048538954057610531)
                ·
                  refine ⟨37811236572808431086415797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25207491048538954057610531 37811236572808431086415797)
                  ·
                    refine ⟨3544803428700790414351481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37811236572808431086415797 3544803428700790414351481)
                    ·
                      refine ⟨2658602571525592810763611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544803428700790414351481 2658602571525592810763611)
                      ·
                        rfl

theorem cell23_5177610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_5177610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177610 prefixEnd_5177610 := by exact prefixLift 5177610
  have htrace : WordTrace (prefixWord ++ tailWord_5177610) baseStart_5177610 baseEnd_5177610 := by
    simpa [prefixWord, tailWord_5177610, baseEnd_5177610] using wordTrace_append hprefix tailTrace_5177610
  have hstable : (prefixWord ++ tailWord_5177610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177610).length < 2 ^ (prefixWord ++ tailWord_5177610).sum := by decide
  have hdescent : baseEnd_5177610 < baseStart_5177610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177660 : List Nat := [2, 2, 2, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_5177660 : Nat := 118140960795 + 5177660 * 2 ^ 59
def prefixEnd_5177660 : Nat := 4983230072969 + 3 ^ 40 * 5177660 * 2
def baseEnd_5177660 : Nat := 2658628245558317615138381

theorem tailTrace_5177660 : CollatzResearch.WordTrace tailWord_5177660 prefixEnd_5177660 2658628245558317615138381 := by
  unfold tailWord_5177660
  simp only [CollatzResearch.WordTrace]
  refine ⟨94422387211114784386233217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125896516281486379181644289 94422387211114784386233217)
  ·
    refine ⟨70816790408336088289674913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94422387211114784386233217 70816790408336088289674913)
    ·
      refine ⟨53112592806252066217256185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70816790408336088289674913 53112592806252066217256185)
      ·
        refine ⟨39834444604689049662942139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53112592806252066217256185 39834444604689049662942139)
        ·
          refine ⟨59751666907033574494413209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39834444604689049662942139 59751666907033574494413209)
          ·
            refine ⟨44813750180275180870809907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59751666907033574494413209 44813750180275180870809907)
            ·
              refine ⟨67220625270412771306214861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44813750180275180870809907 67220625270412771306214861)
              ·
                refine ⟨25207734476404789239830573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67220625270412771306214861 25207734476404789239830573)
                ·
                  refine ⟨9452900428651795964936465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25207734476404789239830573 9452900428651795964936465)
                  ·
                    refine ⟨7089675321488846973702349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9452900428651795964936465 7089675321488846973702349)
                    ·
                      refine ⟨2658628245558317615138381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7089675321488846973702349 2658628245558317615138381)
                      ·
                        rfl

theorem cell23_5177660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_5177660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177660 prefixEnd_5177660 := by exact prefixLift 5177660
  have htrace : WordTrace (prefixWord ++ tailWord_5177660) baseStart_5177660 baseEnd_5177660 := by
    simpa [prefixWord, tailWord_5177660, baseEnd_5177660] using wordTrace_append hprefix tailTrace_5177660
  have hstable : (prefixWord ++ tailWord_5177660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177660).length < 2 ^ (prefixWord ++ tailWord_5177660).sum := by decide
  have hdescent : baseEnd_5177660 < baseStart_5177660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177668 : List Nat := [2, 3, 4, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_5177668 : Nat := 118140960795 + 5177668 * 2 ^ 59
def prefixEnd_5177668 : Nat := 4983230072969 + 3 ^ 40 * 5177668 * 2
def baseEnd_5177668 : Nat := 2658632353403553583838345

theorem tailTrace_5177668 : CollatzResearch.WordTrace tailWord_5177668 prefixEnd_5177668 2658632353403553583838345 := by
  unfold tailWord_5177668
  simp only [CollatzResearch.WordTrace]
  refine ⟨94422533103100293069378829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125896710804133724092505105 94422533103100293069378829)
  ·
    refine ⟨35408449913662609901017061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94422533103100293069378829 35408449913662609901017061)
    ·
      refine ⟨6639084358811739356440699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35408449913662609901017061 6639084358811739356440699)
      ·
        refine ⟨9958626538217609034661049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6639084358811739356440699 9958626538217609034661049)
        ·
          refine ⟨7468969903663206775995787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9958626538217609034661049 7468969903663206775995787)
          ·
            refine ⟨11203454855494810163993681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7468969903663206775995787 11203454855494810163993681)
            ·
              refine ⟨8402591141621107622995261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11203454855494810163993681 8402591141621107622995261)
              ·
                refine ⟨3150971678107915358623223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8402591141621107622995261 3150971678107915358623223)
                ·
                  refine ⟨4726457517161873037934835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3150971678107915358623223 4726457517161873037934835)
                  ·
                    refine ⟨7089686275742809556902253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4726457517161873037934835 7089686275742809556902253)
                    ·
                      refine ⟨2658632353403553583838345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7089686275742809556902253 2658632353403553583838345)
                      ·
                        rfl

theorem cell23_5177668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_5177668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177668 prefixEnd_5177668 := by exact prefixLift 5177668
  have htrace : WordTrace (prefixWord ++ tailWord_5177668) baseStart_5177668 baseEnd_5177668 := by
    simpa [prefixWord, tailWord_5177668, baseEnd_5177668] using wordTrace_append hprefix tailTrace_5177668
  have hstable : (prefixWord ++ tailWord_5177668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177668).length < 2 ^ (prefixWord ++ tailWord_5177668).sum := by decide
  have hdescent : baseEnd_5177668 < baseStart_5177668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177684 : List Nat := [2, 4, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_5177684 : Nat := 118140960795 + 5177684 * 2 ^ 59
def prefixEnd_5177684 : Nat := 4983230072969 + 3 ^ 40 * 5177684 * 2
def baseEnd_5177684 : Nat := 886213523031341840412757

theorem tailTrace_5177684 : CollatzResearch.WordTrace tailWord_5177684 prefixEnd_5177684 886213523031341840412757 := by
  unfold tailWord_5177684
  simp only [CollatzResearch.WordTrace]
  refine ⟨94422824887071310435670053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125897099849428413914226737 94422824887071310435670053)
  ·
    refine ⟨17704279666325870706688135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94422824887071310435670053 17704279666325870706688135)
    ·
      refine ⟨26556419499488806060032203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17704279666325870706688135 26556419499488806060032203)
      ·
        refine ⟨39834629249233209090048305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26556419499488806060032203 39834629249233209090048305)
        ·
          refine ⟨29875971936924906817536229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39834629249233209090048305 29875971936924906817536229)
          ·
            refine ⟨5601744738173420028288043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29875971936924906817536229 5601744738173420028288043)
            ·
              refine ⟨8402617107260130042432065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601744738173420028288043 8402617107260130042432065)
              ·
                refine ⟨6301962830445097531824049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8402617107260130042432065 6301962830445097531824049)
                ·
                  refine ⟨4726472122833823148868037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6301962830445097531824049 4726472122833823148868037)
                  ·
                    refine ⟨886213523031341840412757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4726472122833823148868037 886213523031341840412757)
                    ·
                      rfl

theorem cell23_5177684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_5177684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177684 prefixEnd_5177684 := by exact prefixLift 5177684
  have htrace : WordTrace (prefixWord ++ tailWord_5177684) baseStart_5177684 baseEnd_5177684 := by
    simpa [prefixWord, tailWord_5177684, baseEnd_5177684] using wordTrace_append hprefix tailTrace_5177684
  have hstable : (prefixWord ++ tailWord_5177684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177684).length < 2 ^ (prefixWord ++ tailWord_5177684).sum := by decide
  have hdescent : baseEnd_5177684 < baseStart_5177684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177758 : List Nat := [4, 3, 1, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_5177758 : Nat := 118140960795 + 5177758 * 2 ^ 59
def prefixEnd_5177758 : Nat := 4983230072969 + 3 ^ 40 * 5177758 * 2
def baseEnd_5177758 : Nat := 2658678566662458231712931

theorem tailTrace_5177758 : CollatzResearch.WordTrace tailWord_5177758 prefixEnd_5177758 2658678566662458231712931 := by
  unfold tailWord_5177758
  simp only [CollatzResearch.WordTrace]
  refine ⟨23606043596984316438691741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125898899183916354339689285 23606043596984316438691741)
  ·
    refine ⟨8852266348869118664509403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23606043596984316438691741 8852266348869118664509403)
    ·
      refine ⟨13278399523303677996764105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8852266348869118664509403 13278399523303677996764105)
      ·
        refine ⟨9958799642477758497573079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13278399523303677996764105 9958799642477758497573079)
        ·
          refine ⟨14938199463716637746359619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9958799642477758497573079 14938199463716637746359619)
          ·
            refine ⟨22407299195574956619539429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14938199463716637746359619 22407299195574956619539429)
            ·
              refine ⟨4201368599170304366163643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22407299195574956619539429 4201368599170304366163643)
              ·
                refine ⟨6302052898755456549245465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201368599170304366163643 6302052898755456549245465)
                ·
                  refine ⟨4726539674066592411934099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6302052898755456549245465 4726539674066592411934099)
                  ·
                    refine ⟨7089809511099888617901149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4726539674066592411934099 7089809511099888617901149)
                    ·
                      refine ⟨2658678566662458231712931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7089809511099888617901149 2658678566662458231712931)
                      ·
                        rfl

theorem cell23_5177758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_5177758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177758 prefixEnd_5177758 := by exact prefixLift 5177758
  have htrace : WordTrace (prefixWord ++ tailWord_5177758) baseStart_5177758 baseEnd_5177758 := by
    simpa [prefixWord, tailWord_5177758, baseEnd_5177758] using wordTrace_append hprefix tailTrace_5177758
  have hstable : (prefixWord ++ tailWord_5177758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177758).length < 2 ^ (prefixWord ++ tailWord_5177758).sum := by decide
  have hdescent : baseEnd_5177758 < baseStart_5177758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177768 : List Nat := [2, 1, 6, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5177768 : Nat := 118140960795 + 5177768 * 2 ^ 59
def prefixEnd_5177768 : Nat := 4983230072969 + 3 ^ 40 * 5177768 * 2
def baseEnd_5177768 : Nat := 2658683701469003192587885

theorem tailTrace_5177768 : CollatzResearch.WordTrace tailWord_5177768 prefixEnd_5177768 2658683701469003192587885 := by
  unfold tailWord_5177768
  simp only [CollatzResearch.WordTrace]
  refine ⟨94424356752919151608698979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125899142337225535478265305 94424356752919151608698979)
  ·
    refine ⟨141636535129378727413048469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94424356752919151608698979 141636535129378727413048469)
    ·
      refine ⟨6639212584189627847486647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 141636535129378727413048469 6639212584189627847486647)
      ·
        refine ⟨9958818876284441771229971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6639212584189627847486647 9958818876284441771229971)
        ·
          refine ⟨14938228314426662656844957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9958818876284441771229971 14938228314426662656844957)
          ·
            refine ⟨5601835617909998496316859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14938228314426662656844957 5601835617909998496316859)
            ·
              refine ⟨8402753426864997744475289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601835617909998496316859 8402753426864997744475289)
              ·
                refine ⟨6302065070148748308356467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8402753426864997744475289 6302065070148748308356467)
                ·
                  refine ⟨9453097605223122462534701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6302065070148748308356467 9453097605223122462534701)
                  ·
                    refine ⟨3544911601958670923450513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9453097605223122462534701 3544911601958670923450513)
                    ·
                      refine ⟨2658683701469003192587885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3544911601958670923450513 2658683701469003192587885)
                      ·
                        rfl

theorem cell23_5177768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5177768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177768 prefixEnd_5177768 := by exact prefixLift 5177768
  have htrace : WordTrace (prefixWord ++ tailWord_5177768) baseStart_5177768 baseEnd_5177768 := by
    simpa [prefixWord, tailWord_5177768, baseEnd_5177768] using wordTrace_append hprefix tailTrace_5177768
  have hstable : (prefixWord ++ tailWord_5177768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177768).length < 2 ^ (prefixWord ++ tailWord_5177768).sum := by decide
  have hdescent : baseEnd_5177768 < baseStart_5177768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177804 : List Nat := [2, 2, 1, 4, 3, 1, 1, 4, 5]
def baseStart_5177804 : Nat := 118140960795 + 5177804 * 2 ^ 59
def prefixEnd_5177804 : Nat := 4983230072969 + 3 ^ 40 * 5177804 * 2
def baseEnd_5177804 : Nat := 295411354085840561304191

theorem tailTrace_5177804 : CollatzResearch.WordTrace tailWord_5177804 prefixEnd_5177804 295411354085840561304191 := by
  unfold tailWord_5177804
  simp only [CollatzResearch.WordTrace]
  refine ⟨94425013266853940682854233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125900017689138587577138977 94425013266853940682854233)
  ·
    refine ⟨70818759950140455512140675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94425013266853940682854233 70818759950140455512140675)
    ·
      refine ⟨106228139925210683268211013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70818759950140455512140675 106228139925210683268211013)
      ·
        refine ⟨19917776235977003112789565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106228139925210683268211013 19917776235977003112789565)
        ·
          refine ⟨7469166088491376167296087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19917776235977003112789565 7469166088491376167296087)
          ·
            refine ⟨11203749132737064250944131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7469166088491376167296087 11203749132737064250944131)
            ·
              refine ⟨16805623699105596376416197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11203749132737064250944131 16805623699105596376416197)
              ·
                refine ⟨3151054443582299320578037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16805623699105596376416197 3151054443582299320578037)
                ·
                  refine ⟨295411354085840561304191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3151054443582299320578037 295411354085840561304191)
                  ·
                    rfl

theorem cell23_5177804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 5].length) (baseStart_5177804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177804 prefixEnd_5177804 := by exact prefixLift 5177804
  have htrace : WordTrace (prefixWord ++ tailWord_5177804) baseStart_5177804 baseEnd_5177804 := by
    simpa [prefixWord, tailWord_5177804, baseEnd_5177804] using wordTrace_append hprefix tailTrace_5177804
  have hstable : (prefixWord ++ tailWord_5177804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177804).length < 2 ^ (prefixWord ++ tailWord_5177804).sum := by decide
  have hdescent : baseEnd_5177804 < baseStart_5177804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177814 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_5177814 : Nat := 118140960795 + 5177814 * 2 ^ 59
def prefixEnd_5177814 : Nat := 4983230072969 + 3 ^ 40 * 5177814 * 2
def baseEnd_5177814 : Nat := 2658707321579110012612673

theorem tailTrace_5177814 : CollatzResearch.WordTrace tailWord_5177814 prefixEnd_5177814 2658707321579110012612673 := by
  unfold tailWord_5177814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11803149453979478317098281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125900260842447768715714997 11803149453979478317098281)
  ·
    refine ⟨8852362090484608737823711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11803149453979478317098281 8852362090484608737823711)
    ·
      refine ⟨13278543135726913106735567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8852362090484608737823711 13278543135726913106735567)
      ·
        refine ⟨19917814703590369660103351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13278543135726913106735567 19917814703590369660103351)
        ·
          refine ⟨29876722055385554490155027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19917814703590369660103351 29876722055385554490155027)
          ·
            refine ⟨44815083083078331735232541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29876722055385554490155027 44815083083078331735232541)
            ·
              refine ⟨16805656156154374400712203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44815083083078331735232541 16805656156154374400712203)
              ·
                refine ⟨25208484234231561601068305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16805656156154374400712203 25208484234231561601068305)
                ·
                  refine ⟨18906363175673671200801229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25208484234231561601068305 18906363175673671200801229)
                  ·
                    refine ⟨7089886190877626700300461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18906363175673671200801229 7089886190877626700300461)
                    ·
                      refine ⟨2658707321579110012612673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7089886190877626700300461 2658707321579110012612673)
                      ·
                        rfl

theorem cell23_5177814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_5177814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177814 prefixEnd_5177814 := by exact prefixLift 5177814
  have htrace : WordTrace (prefixWord ++ tailWord_5177814) baseStart_5177814 baseEnd_5177814 := by
    simpa [prefixWord, tailWord_5177814, baseEnd_5177814] using wordTrace_append hprefix tailTrace_5177814
  have hstable : (prefixWord ++ tailWord_5177814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177814).length < 2 ^ (prefixWord ++ tailWord_5177814).sum := by decide
  have hdescent : baseEnd_5177814 < baseStart_5177814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177834 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_5177834 : Nat := 118140960795 + 5177834 * 2 ^ 59
def prefixEnd_5177834 : Nat := 4983230072969 + 3 ^ 40 * 5177834 * 2
def baseEnd_5177834 : Nat := 886239197064066644787527

theorem tailTrace_5177834 : CollatzResearch.WordTrace tailWord_5177834 prefixEnd_5177834 886239197064066644787527 := by
  unfold tailWord_5177834
  simp only [CollatzResearch.WordTrace]
  refine ⟨47212780180899799122325139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125900747149066130992867037 47212780180899799122325139)
  ·
    refine ⟨70819170271349698683487709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47212780180899799122325139 70819170271349698683487709)
    ·
      refine ⟨26557188851756137006307891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70819170271349698683487709 26557188851756137006307891)
      ·
        refine ⟨39835783277634205509461837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26557188851756137006307891 39835783277634205509461837)
        ·
          refine ⟨14938418729112827066048189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39835783277634205509461837 14938418729112827066048189)
          ·
            refine ⟨5601907023417310149768071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14938418729112827066048189 5601907023417310149768071)
            ·
              refine ⟨8402860535125965224652107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601907023417310149768071 8402860535125965224652107)
              ·
                refine ⟨12604290802688947836978161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8402860535125965224652107 12604290802688947836978161)
                ·
                  refine ⟨9453218102016710877733621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12604290802688947836978161 9453218102016710877733621)
                  ·
                    refine ⟨886239197064066644787527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9453218102016710877733621 886239197064066644787527)
                    ·
                      rfl

theorem cell23_5177834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_5177834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177834 prefixEnd_5177834 := by exact prefixLift 5177834
  have htrace : WordTrace (prefixWord ++ tailWord_5177834) baseStart_5177834 baseEnd_5177834 := by
    simpa [prefixWord, tailWord_5177834, baseEnd_5177834] using wordTrace_append hprefix tailTrace_5177834
  have hstable : (prefixWord ++ tailWord_5177834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177834).length < 2 ^ (prefixWord ++ tailWord_5177834).sum := by decide
  have hdescent : baseEnd_5177834 < baseStart_5177834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177898 : List Nat := [3, 1, 4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_5177898 : Nat := 118140960795 + 5177898 * 2 ^ 59
def prefixEnd_5177898 : Nat := 4983230072969 + 3 ^ 40 * 5177898 * 2
def baseEnd_5177898 : Nat := 886250151318029227987429

theorem tailTrace_5177898 : CollatzResearch.WordTrace tailWord_5177898 prefixEnd_5177898 886250151318029227987429 := by
  unfold tailWord_5177898
  simp only [CollatzResearch.WordTrace]
  refine ⟨47213363748841833854907587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125902303330244890279753565 47213363748841833854907587)
  ·
    refine ⟨70820045623262750782361381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47213363748841833854907587 70820045623262750782361381)
    ·
      refine ⟨13278758554361765771692759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70820045623262750782361381 13278758554361765771692759)
      ·
        refine ⟨19918137831542648657539139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13278758554361765771692759 19918137831542648657539139)
        ·
          refine ⟨29877206747313972986308709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19918137831542648657539139 29877206747313972986308709)
          ·
            refine ⟨5601976265121369934932883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29877206747313972986308709 5601976265121369934932883)
            ·
              refine ⟨8402964397682054902399325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5601976265121369934932883 8402964397682054902399325)
              ·
                refine ⟨3151111649130770588399747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8402964397682054902399325 3151111649130770588399747)
                ·
                  refine ⟨4726667473696155882599621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151111649130770588399747 4726667473696155882599621)
                  ·
                    refine ⟨886250151318029227987429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4726667473696155882599621 886250151318029227987429)
                    ·
                      rfl

theorem cell23_5177898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_5177898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177898 prefixEnd_5177898 := by exact prefixLift 5177898
  have htrace : WordTrace (prefixWord ++ tailWord_5177898) baseStart_5177898 baseEnd_5177898 := by
    simpa [prefixWord, tailWord_5177898, baseEnd_5177898] using wordTrace_append hprefix tailTrace_5177898
  have hstable : (prefixWord ++ tailWord_5177898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177898).length < 2 ^ (prefixWord ++ tailWord_5177898).sum := by decide
  have hdescent : baseEnd_5177898 < baseStart_5177898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177907 : List Nat := [1, 1, 1, 2, 4, 2, 1, 5, 1, 5]
def baseStart_5177907 : Nat := 118140960795 + 5177907 * 2 ^ 59
def prefixEnd_5177907 : Nat := 4983230072969 + 3 ^ 40 * 5177907 * 2
def baseEnd_5177907 : Nat := 886251691759992716249915

theorem tailTrace_5177907 : CollatzResearch.WordTrace tailWord_5177907 prefixEnd_5177907 886251691759992716249915 := by
  unfold tailWord_5177907
  simp only [CollatzResearch.WordTrace]
  refine ⟨188853783252334729956707975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125902522168223153304471983 188853783252334729956707975)
  ·
    refine ⟨283280674878502094935061963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188853783252334729956707975 283280674878502094935061963)
    ·
      refine ⟨424921012317753142402592945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283280674878502094935061963 424921012317753142402592945)
      ·
        refine ⟨318690759238314856801944709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424921012317753142402592945 318690759238314856801944709)
        ·
          refine ⟨59754517357184035650364633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 318690759238314856801944709 59754517357184035650364633)
          ·
            refine ⟨44815888017888026737773475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59754517357184035650364633 44815888017888026737773475)
            ·
              refine ⟨67223832026832040106660213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44815888017888026737773475 67223832026832040106660213)
              ·
                refine ⟨6302234252515503759999395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67223832026832040106660213 6302234252515503759999395)
                ·
                  refine ⟨9453351378773255639999093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6302234252515503759999395 9453351378773255639999093)
                  ·
                    refine ⟨886251691759992716249915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9453351378773255639999093 886251691759992716249915)
                    ·
                      rfl

theorem cell23_5177907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 5].length) (baseStart_5177907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177907 prefixEnd_5177907 := by exact prefixLift 5177907
  have htrace : WordTrace (prefixWord ++ tailWord_5177907) baseStart_5177907 baseEnd_5177907 := by
    simpa [prefixWord, tailWord_5177907, baseEnd_5177907] using wordTrace_append hprefix tailTrace_5177907
  have hstable : (prefixWord ++ tailWord_5177907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177907).length < 2 ^ (prefixWord ++ tailWord_5177907).sum := by decide
  have hdescent : baseEnd_5177907 < baseStart_5177907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177908 : List Nat := [2, 5, 1, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5177908 : Nat := 118140960795 + 5177908 * 2 ^ 59
def prefixEnd_5177908 : Nat := 4983230072969 + 3 ^ 40 * 5177908 * 2
def baseEnd_5177908 : Nat := 2658755588760632644837241

theorem tailTrace_5177908 : CollatzResearch.WordTrace tailWord_5177908 prefixEnd_5177908 2658755588760632644837241 := by
  unfold tailWord_5177908
  simp only [CollatzResearch.WordTrace]
  refine ⟨94426909862665553563747189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125902546483554071418329585 94426909862665553563747189)
  ·
    refine ⟨8852522799624895646601299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94426909862665553563747189 8852522799624895646601299)
    ·
      refine ⟨13278784199437343469901949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8852522799624895646601299 13278784199437343469901949)
      ·
        refine ⟨4979544074789003801213231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13278784199437343469901949 4979544074789003801213231)
        ·
          refine ⟨7469316112183505701819847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4979544074789003801213231 7469316112183505701819847)
          ·
            refine ⟨11203974168275258552729771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7469316112183505701819847 11203974168275258552729771)
            ·
              refine ⟨16805961252412887829094657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11203974168275258552729771 16805961252412887829094657)
              ·
                refine ⟨12604470939309665871820993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16805961252412887829094657 12604470939309665871820993)
                ·
                  refine ⟨9453353204482249403865745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12604470939309665871820993 9453353204482249403865745)
                  ·
                    refine ⟨7090014903361687052899309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9453353204482249403865745 7090014903361687052899309)
                    ·
                      refine ⟨2658755588760632644837241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7090014903361687052899309 2658755588760632644837241)
                      ·
                        rfl

theorem cell23_5177908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5177908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177908 prefixEnd_5177908 := by exact prefixLift 5177908
  have htrace : WordTrace (prefixWord ++ tailWord_5177908) baseStart_5177908 baseEnd_5177908 := by
    simpa [prefixWord, tailWord_5177908, baseEnd_5177908] using wordTrace_append hprefix tailTrace_5177908
  have hstable : (prefixWord ++ tailWord_5177908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177908).length < 2 ^ (prefixWord ++ tailWord_5177908).sum := by decide
  have hdescent : baseEnd_5177908 < baseStart_5177908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177914 : List Nat := [3, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2]
def baseStart_5177914 : Nat := 118140960795 + 5177914 * 2 ^ 59
def prefixEnd_5177914 : Nat := 4983230072969 + 3 ^ 40 * 5177914 * 2
def baseEnd_5177914 : Nat := 2658758669644559621362213

theorem tailTrace_5177914 : CollatzResearch.WordTrace tailWord_5177914 prefixEnd_5177914 2658758669644559621362213 := by
  unfold tailWord_5177914
  simp only [CollatzResearch.WordTrace]
  refine ⟨47213509640827342538053199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125902692375539580101475197 47213509640827342538053199)
  ·
    refine ⟨70820264461241013807079799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47213509640827342538053199 70820264461241013807079799)
    ·
      refine ⟨106230396691861520710619699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70820264461241013807079799 106230396691861520710619699)
      ·
        refine ⟨159345595037792281065929549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106230396691861520710619699 159345595037792281065929549)
        ·
          refine ⟨59754598139172105399723581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159345595037792281065929549 59754598139172105399723581)
          ·
            refine ⟨22407974302189539524896343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59754598139172105399723581 22407974302189539524896343)
            ·
              refine ⟨33611961453284309287344515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22407974302189539524896343 33611961453284309287344515)
              ·
                refine ⟨50417942179926463931016773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33611961453284309287344515 50417942179926463931016773)
                ·
                  refine ⟨9453364158736211987065645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50417942179926463931016773 9453364158736211987065645)
                  ·
                    refine ⟨3545011559526079495149617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9453364158736211987065645 3545011559526079495149617)
                    ·
                      refine ⟨2658758669644559621362213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545011559526079495149617 2658758669644559621362213)
                      ·
                        rfl

theorem cell23_5177914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_5177914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177914 prefixEnd_5177914 := by exact prefixLift 5177914
  have htrace : WordTrace (prefixWord ++ tailWord_5177914) baseStart_5177914 baseEnd_5177914 := by
    simpa [prefixWord, tailWord_5177914, baseEnd_5177914] using wordTrace_append hprefix tailTrace_5177914
  have hstable : (prefixWord ++ tailWord_5177914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177914).length < 2 ^ (prefixWord ++ tailWord_5177914).sum := by decide
  have hdescent : baseEnd_5177914 < baseStart_5177914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177921 : List Nat := [1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_5177921 : Nat := 118140960795 + 5177921 * 2 ^ 59
def prefixEnd_5177921 : Nat := 4983230072969 + 3 ^ 40 * 5177921 * 2
def baseEnd_5177921 : Nat := 2658762264009141093974681

theorem tailTrace_5177921 : CollatzResearch.WordTrace tailWord_5177921 prefixEnd_5177921 2658762264009141093974681 := by
  unfold tailWord_5177921
  simp only [CollatzResearch.WordTrace]
  refine ⟨188854293874284010347717617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125902862582856006898478411 188854293874284010347717617)
  ·
    refine ⟨141640720405713007760788213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188854293874284010347717617 141640720405713007760788213)
    ·
      refine ⟨13278817538035594477573895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 141640720405713007760788213 13278817538035594477573895)
      ·
        refine ⟨19918226307053391716360843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13278817538035594477573895 19918226307053391716360843)
        ·
          refine ⟨29877339460580087574541265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19918226307053391716360843 29877339460580087574541265)
          ·
            refine ⟨22408004595435065680905949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29877339460580087574541265 22408004595435065680905949)
            ·
              refine ⟨8403001723288149630339731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22408004595435065680905949 8403001723288149630339731)
              ·
                refine ⟨12604502584932224445509597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8403001723288149630339731 12604502584932224445509597)
                ·
                  refine ⟨4726688469349584167066099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12604502584932224445509597 4726688469349584167066099)
                  ·
                    refine ⟨7090032704024376250599149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4726688469349584167066099 7090032704024376250599149)
                    ·
                      refine ⟨2658762264009141093974681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7090032704024376250599149 2658762264009141093974681)
                      ·
                        rfl

theorem cell23_5177921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_5177921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177921 prefixEnd_5177921 := by exact prefixLift 5177921
  have htrace : WordTrace (prefixWord ++ tailWord_5177921) baseStart_5177921 baseEnd_5177921 := by
    simpa [prefixWord, tailWord_5177921, baseEnd_5177921] using wordTrace_append hprefix tailTrace_5177921
  have hstable : (prefixWord ++ tailWord_5177921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177921).length < 2 ^ (prefixWord ++ tailWord_5177921).sum := by decide
  have hdescent : baseEnd_5177921 < baseStart_5177921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177944 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 1, 1, 4]
def baseStart_5177944 : Nat := 118140960795 + 5177944 * 2 ^ 59
def prefixEnd_5177944 : Nat := 4983230072969 + 3 ^ 40 * 5177944 * 2
def baseEnd_5177944 : Nat := 2658774074064194503987075

theorem tailTrace_5177944 : CollatzResearch.WordTrace tailWord_5177944 prefixEnd_5177944 2658774074064194503987075 := by
  unfold tailWord_5177944
  simp only [CollatzResearch.WordTrace]
  refine ⟨94427566376600342637902443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125903421835467123517203257 94427566376600342637902443)
  ·
    refine ⟨141641349564900513956853665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94427566376600342637902443 141641349564900513956853665)
    ·
      refine ⟨106231012173675385467640249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141641349564900513956853665 106231012173675385467640249)
      ·
        refine ⟨79673259130256539100730187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106231012173675385467640249 79673259130256539100730187)
        ·
          refine ⟨119509888695384808651095281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79673259130256539100730187 119509888695384808651095281)
          ·
            refine ⟨89632416521538606488321461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119509888695384808651095281 89632416521538606488321461)
            ·
              refine ⟨8403039048894244358280137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89632416521538606488321461 8403039048894244358280137)
              ·
                refine ⟨6302279286670683268710103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8403039048894244358280137 6302279286670683268710103)
                ·
                  refine ⟨9453418930006024903065155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6302279286670683268710103 9453418930006024903065155)
                  ·
                    refine ⟨14180128395009037354597733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9453418930006024903065155 14180128395009037354597733)
                    ·
                      refine ⟨2658774074064194503987075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14180128395009037354597733 2658774074064194503987075)
                      ·
                        rfl

theorem cell23_5177944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 1, 4].length) (baseStart_5177944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177944 prefixEnd_5177944 := by exact prefixLift 5177944
  have htrace : WordTrace (prefixWord ++ tailWord_5177944) baseStart_5177944 baseEnd_5177944 := by
    simpa [prefixWord, tailWord_5177944, baseEnd_5177944] using wordTrace_append hprefix tailTrace_5177944
  have hstable : (prefixWord ++ tailWord_5177944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177944).length < 2 ^ (prefixWord ++ tailWord_5177944).sum := by decide
  have hdescent : baseEnd_5177944 < baseStart_5177944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177948 : List Nat := [2, 2, 4, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_5177948 : Nat := 118140960795 + 5177948 * 2 ^ 59
def prefixEnd_5177948 : Nat := 4983230072969 + 3 ^ 40 * 5177948 * 2
def baseEnd_5177948 : Nat := 2658776127986812488337057

theorem tailTrace_5177948 : CollatzResearch.WordTrace tailWord_5177948 prefixEnd_5177948 2658776127986812488337057 := by
  unfold tailWord_5177948
  simp only [CollatzResearch.WordTrace]
  refine ⟨94427639322593096979475249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125903519096790795972633665 94427639322593096979475249)
  ·
    refine ⟨70820729491944822734606437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94427639322593096979475249 70820729491944822734606437)
    ·
      refine ⟨13278886779739654262738707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70820729491944822734606437 13278886779739654262738707)
      ·
        refine ⟨19918330169609481394108061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13278886779739654262738707 19918330169609481394108061)
        ·
          refine ⟨7469373813603555522790523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19918330169609481394108061 7469373813603555522790523)
          ·
            refine ⟨11204060720405333284185785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7469373813603555522790523 11204060720405333284185785)
            ·
              refine ⟨8403045540303999963139339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11204060720405333284185785 8403045540303999963139339)
              ·
                refine ⟨12604568310455999944709009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8403045540303999963139339 12604568310455999944709009)
                ·
                  refine ⟨9453426232841999958531757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12604568310455999944709009 9453426232841999958531757)
                  ·
                    refine ⟨3545034837315749984449409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9453426232841999958531757 3545034837315749984449409)
                    ·
                      refine ⟨2658776127986812488337057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545034837315749984449409 2658776127986812488337057)
                      ·
                        rfl

theorem cell23_5177948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_5177948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177948 prefixEnd_5177948 := by exact prefixLift 5177948
  have htrace : WordTrace (prefixWord ++ tailWord_5177948) baseStart_5177948 baseEnd_5177948 := by
    simpa [prefixWord, tailWord_5177948, baseEnd_5177948] using wordTrace_append hprefix tailTrace_5177948
  have hstable : (prefixWord ++ tailWord_5177948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177948).length < 2 ^ (prefixWord ++ tailWord_5177948).sum := by decide
  have hdescent : baseEnd_5177948 < baseStart_5177948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5177964 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 3]
def baseStart_5177964 : Nat := 118140960795 + 5177964 * 2 ^ 59
def prefixEnd_5177964 : Nat := 4983230072969 + 3 ^ 40 * 5177964 * 2
def baseEnd_5177964 : Nat := 2658784343677284425736983

theorem tailTrace_5177964 : CollatzResearch.WordTrace tailWord_5177964 prefixEnd_5177964 2658784343677284425736983 := by
  unfold tailWord_5177964
  simp only [CollatzResearch.WordTrace]
  refine ⟨94427931106564114345766473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125903908142085485794355297 94427931106564114345766473)
  ·
    refine ⟨70820948329923085759324855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94427931106564114345766473 70820948329923085759324855)
    ·
      refine ⟨106231422494884628638987283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70820948329923085759324855 106231422494884628638987283)
      ·
        refine ⟨159347133742326942958480925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106231422494884628638987283 159347133742326942958480925)
        ·
          refine ⟨59755175153372603609430347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159347133742326942958480925 59755175153372603609430347)
          ·
            refine ⟨89632762730058905414145521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59755175153372603609430347 89632762730058905414145521)
            ·
              refine ⟨67224572047544179060609141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89632762730058905414145521 67224572047544179060609141)
              ·
                refine ⟨6302303629457266786932107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67224572047544179060609141 6302303629457266786932107)
                ·
                  refine ⟨9453455444185900180398161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6302303629457266786932107 9453455444185900180398161)
                  ·
                    refine ⟨7090091583139425135298621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9453455444185900180398161 7090091583139425135298621)
                    ·
                      refine ⟨2658784343677284425736983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7090091583139425135298621 2658784343677284425736983)
                      ·
                        rfl

theorem cell23_5177964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_5177964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5177964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5177964 prefixEnd_5177964 := by exact prefixLift 5177964
  have htrace : WordTrace (prefixWord ++ tailWord_5177964) baseStart_5177964 baseEnd_5177964 := by
    simpa [prefixWord, tailWord_5177964, baseEnd_5177964] using wordTrace_append hprefix tailTrace_5177964
  have hstable : (prefixWord ++ tailWord_5177964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5177964).length < 2 ^ (prefixWord ++ tailWord_5177964).sum := by decide
  have hdescent : baseEnd_5177964 < baseStart_5177964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5177964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178007 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_5178007 : Nat := 118140960795 + 5178007 * 2 ^ 59
def prefixEnd_5178007 : Nat := 4983230072969 + 3 ^ 40 * 5178007 * 2
def baseEnd_5178007 : Nat := 2658806423345427757499285

theorem tailTrace_5178007 : CollatzResearch.WordTrace tailWord_5178007 prefixEnd_5178007 2658806423345427757499285 := by
  unfold tailWord_5178007
  simp only [CollatzResearch.WordTrace]
  refine ⟨188857430551972447035348275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125904953701314964690232183 188857430551972447035348275)
  ·
    refine ⟨283286145827958670553022413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188857430551972447035348275 283286145827958670553022413)
    ·
      refine ⟨106232304685484501457383405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283286145827958670553022413 106232304685484501457383405)
      ·
        refine ⟨39837114257056688046518777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106232304685484501457383405 39837114257056688046518777)
        ·
          refine ⟨29877835692792516034889083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39837114257056688046518777 29877835692792516034889083)
          ·
            refine ⟨44816753539188774052333625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29877835692792516034889083 44816753539188774052333625)
            ·
              refine ⟨33612565154391580539250219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44816753539188774052333625 33612565154391580539250219)
              ·
                refine ⟨50418847731587370808875329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33612565154391580539250219 50418847731587370808875329)
                ·
                  refine ⟨37814135798690528106656497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50418847731587370808875329 37814135798690528106656497)
                  ·
                    refine ⟨28360601849017896079992373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37814135798690528106656497 28360601849017896079992373)
                    ·
                      refine ⟨2658806423345427757499285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28360601849017896079992373 2658806423345427757499285)
                      ·
                        rfl

theorem cell23_5178007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_5178007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178007 prefixEnd_5178007 := by exact prefixLift 5178007
  have htrace : WordTrace (prefixWord ++ tailWord_5178007) baseStart_5178007 baseEnd_5178007 := by
    simpa [prefixWord, tailWord_5178007, baseEnd_5178007] using wordTrace_append hprefix tailTrace_5178007
  have hstable : (prefixWord ++ tailWord_5178007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178007).length < 2 ^ (prefixWord ++ tailWord_5178007).sum := by decide
  have hdescent : baseEnd_5178007 < baseStart_5178007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178117 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 2, 8]
def baseStart_5178117 : Nat := 118140960795 + 5178117 * 2 ^ 59
def prefixEnd_5178117 : Nat := 4983230072969 + 3 ^ 40 * 5178117 * 2
def baseEnd_5178117 : Nat := 886287635405807442374593

theorem tailTrace_5178117 : CollatzResearch.WordTrace tailWord_5178117 prefixEnd_5178117 886287635405807442374593 := by
  unfold tailWord_5178117
  simp only [CollatzResearch.WordTrace]
  refine ⟨188861442581573935821852605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125907628387715957214568403 188861442581573935821852605)
  ·
    refine ⟨70823040968090225933194727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188861442581573935821852605 70823040968090225933194727)
    ·
      refine ⟨106234561452135338899792091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70823040968090225933194727 106234561452135338899792091)
      ·
        refine ⟨159351842178203008349688137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106234561452135338899792091 159351842178203008349688137)
        ·
          refine ⟨119513881633652256262266103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159351842178203008349688137 119513881633652256262266103)
          ·
            refine ⟨179270822450478384393399155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119513881633652256262266103 179270822450478384393399155)
            ·
              refine ⟨268906233675717576590098733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179270822450478384393399155 268906233675717576590098733)
              ·
                refine ⟨100839837628394091221287025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268906233675717576590098733 100839837628394091221287025)
                ·
                  refine ⟨75629878221295568415965269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100839837628394091221287025 75629878221295568415965269)
                  ·
                    refine ⟨886287635405807442374593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75629878221295568415965269 886287635405807442374593)
                    ·
                      rfl

theorem cell23_5178117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_5178117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178117 prefixEnd_5178117 := by exact prefixLift 5178117
  have htrace : WordTrace (prefixWord ++ tailWord_5178117) baseStart_5178117 baseEnd_5178117 := by
    simpa [prefixWord, tailWord_5178117, baseEnd_5178117] using wordTrace_append hprefix tailTrace_5178117
  have hstable : (prefixWord ++ tailWord_5178117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178117).length < 2 ^ (prefixWord ++ tailWord_5178117).sum := by decide
  have hdescent : baseEnd_5178117 < baseStart_5178117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178158 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5178158 : Nat := 118140960795 + 5178158 * 2 ^ 59
def prefixEnd_5178158 : Nat := 4983230072969 + 3 ^ 40 * 5178158 * 2
def baseEnd_5178158 : Nat := 2658883958924256666711091

theorem tailTrace_5178158 : CollatzResearch.WordTrace tailWord_5178158 prefixEnd_5178158 2658883958924256666711091 := by
  unfold tailWord_5178158
  simp only [CollatzResearch.WordTrace]
  refine ⟨23607867246803174978011891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125908625316283599882730085 23607867246803174978011891)
  ·
    refine ⟨35411800870204762467017837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23607867246803174978011891 35411800870204762467017837)
    ·
      refine ⟨13279425326326785925131689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35411800870204762467017837 13279425326326785925131689)
      ·
        refine ⟨9959568994745089443848767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13279425326326785925131689 9959568994745089443848767)
        ·
          refine ⟨14939353492117634165773151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9959568994745089443848767 14939353492117634165773151)
          ·
            refine ⟨22409030238176451248659727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14939353492117634165773151 22409030238176451248659727)
            ·
              refine ⟨33613545357264676872989591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22409030238176451248659727 33613545357264676872989591)
              ·
                refine ⟨50420318035897015309484387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33613545357264676872989591 50420318035897015309484387)
                ·
                  refine ⟨75630477053845522964226581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50420318035897015309484387 75630477053845522964226581)
                  ·
                    refine ⟨3545178611899008888948121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75630477053845522964226581 3545178611899008888948121)
                    ·
                      refine ⟨2658883958924256666711091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545178611899008888948121 2658883958924256666711091)
                      ·
                        rfl

theorem cell23_5178158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5178158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178158 prefixEnd_5178158 := by exact prefixLift 5178158
  have htrace : WordTrace (prefixWord ++ tailWord_5178158) baseStart_5178158 baseEnd_5178158 := by
    simpa [prefixWord, tailWord_5178158, baseEnd_5178158] using wordTrace_append hprefix tailTrace_5178158
  have hstable : (prefixWord ++ tailWord_5178158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178158).length < 2 ^ (prefixWord ++ tailWord_5178158).sum := by decide
  have hdescent : baseEnd_5178158 < baseStart_5178158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178208 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 3, 1, 3]
def baseStart_5178208 : Nat := 118140960795 + 5178208 * 2 ^ 59
def prefixEnd_5178208 : Nat := 4983230072969 + 3 ^ 40 * 5178208 * 2
def baseEnd_5178208 : Nat := 2658909632956981471085861

theorem tailTrace_5178208 : CollatzResearch.WordTrace tailWord_5178208 prefixEnd_5178208 2658909632956981471085861 := by
  unfold tailWord_5178208
  simp only [CollatzResearch.WordTrace]
  refine ⟨94432380812122129181707639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125909841082829505575610185 94432380812122129181707639)
  ·
    refine ⟨141648571218183193772561459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94432380812122129181707639 141648571218183193772561459)
    ·
      refine ⟨212472856827274790658842189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141648571218183193772561459 212472856827274790658842189)
      ·
        refine ⟨79677321310228046497065821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 212472856827274790658842189 79677321310228046497065821)
        ·
          refine ⟨29878995491335517436399683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79677321310228046497065821 29878995491335517436399683)
          ·
            refine ⟨44818493237003276154599525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29878995491335517436399683 44818493237003276154599525)
            ·
              refine ⟨8403467481938114278987411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44818493237003276154599525 8403467481938114278987411)
              ·
                refine ⟨12605201222907171418481117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8403467481938114278987411 12605201222907171418481117)
                ·
                  refine ⟨4726950458590189281930419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12605201222907171418481117 4726950458590189281930419)
                  ·
                    refine ⟨7090425687885283922895629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4726950458590189281930419 7090425687885283922895629)
                    ·
                      refine ⟨2658909632956981471085861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7090425687885283922895629 2658909632956981471085861)
                      ·
                        rfl

theorem cell23_5178208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_5178208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178208 prefixEnd_5178208 := by exact prefixLift 5178208
  have htrace : WordTrace (prefixWord ++ tailWord_5178208) baseStart_5178208 baseEnd_5178208 := by
    simpa [prefixWord, tailWord_5178208, baseEnd_5178208] using wordTrace_append hprefix tailTrace_5178208
  have hstable : (prefixWord ++ tailWord_5178208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178208).length < 2 ^ (prefixWord ++ tailWord_5178208).sum := by decide
  have hdescent : baseEnd_5178208 < baseStart_5178208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178234 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_5178234 : Nat := 118140960795 + 5178234 * 2 ^ 59
def prefixEnd_5178234 : Nat := 4983230072969 + 3 ^ 40 * 5178234 * 2
def baseEnd_5178234 : Nat := 2658922983453998369360741

theorem tailTrace_5178234 : CollatzResearch.WordTrace tailWord_5178234 prefixEnd_5178234 2658922983453998369360741 := by
  unfold tailWord_5178234
  simp only [CollatzResearch.WordTrace]
  refine ⟨47216427480537516200965439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125910473281433376535907837 47216427480537516200965439)
  ·
    refine ⟨70824641220806274301448159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47216427480537516200965439 70824641220806274301448159)
    ·
      refine ⟨106236961831209411452172239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70824641220806274301448159 106236961831209411452172239)
      ·
        refine ⟨159355442746814117178258359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106236961831209411452172239 159355442746814117178258359)
        ·
          refine ⟨239033164120221175767387539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159355442746814117178258359 239033164120221175767387539)
          ·
            refine ⟨358549746180331763651081309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239033164120221175767387539 358549746180331763651081309)
            ·
              refine ⟨134456154817624411369155491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358549746180331763651081309 134456154817624411369155491)
              ·
                refine ⟨201684232226436617053733237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134456154817624411369155491 201684232226436617053733237)
                ·
                  refine ⟨18907896771228432848787491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201684232226436617053733237 18907896771228432848787491)
                  ·
                    refine ⟨28361845156842649273181237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18907896771228432848787491 28361845156842649273181237)
                    ·
                      refine ⟨2658922983453998369360741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28361845156842649273181237 2658922983453998369360741)
                      ·
                        rfl

theorem cell23_5178234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_5178234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178234 prefixEnd_5178234 := by exact prefixLift 5178234
  have htrace : WordTrace (prefixWord ++ tailWord_5178234) baseStart_5178234 baseEnd_5178234 := by
    simpa [prefixWord, tailWord_5178234, baseEnd_5178234] using wordTrace_append hprefix tailTrace_5178234
  have hstable : (prefixWord ++ tailWord_5178234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178234).length < 2 ^ (prefixWord ++ tailWord_5178234).sum := by decide
  have hdescent : baseEnd_5178234 < baseStart_5178234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178248 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 1, 1, 4]
def baseStart_5178248 : Nat := 118140960795 + 5178248 * 2 ^ 59
def prefixEnd_5178248 : Nat := 4983230072969 + 3 ^ 40 * 5178248 * 2
def baseEnd_5178248 : Nat := 2658930172183161314585677

theorem tailTrace_5178248 : CollatzResearch.WordTrace tailWord_5178248 prefixEnd_5178248 2658930172183161314585677 := by
  unfold tailWord_5178248
  simp only [CollatzResearch.WordTrace]
  refine ⟨94433110272049672597435699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125910813696066230129914265 94433110272049672597435699)
  ·
    refine ⟨141649665408074508896153549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94433110272049672597435699 141649665408074508896153549)
    ·
      refine ⟨53118624528027940836057581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141649665408074508896153549 53118624528027940836057581)
      ·
        refine ⟨19919484198010477813521593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53118624528027940836057581 19919484198010477813521593)
        ·
          refine ⟨14939613148507858360141195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19919484198010477813521593 14939613148507858360141195)
          ·
            refine ⟨22409419722761787540211793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14939613148507858360141195 22409419722761787540211793)
            ·
              refine ⟨16807064792071340655158845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22409419722761787540211793 16807064792071340655158845)
              ·
                refine ⟨6302649297026752745684567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16807064792071340655158845 6302649297026752745684567)
                ·
                  refine ⟨9453973945540129118526851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6302649297026752745684567 9453973945540129118526851)
                  ·
                    refine ⟨14180960918310193677790277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9453973945540129118526851 14180960918310193677790277)
                    ·
                      refine ⟨2658930172183161314585677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14180960918310193677790277 2658930172183161314585677)
                      ·
                        rfl

theorem cell23_5178248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_5178248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178248 prefixEnd_5178248 := by exact prefixLift 5178248
  have htrace : WordTrace (prefixWord ++ tailWord_5178248) baseStart_5178248 baseEnd_5178248 := by
    simpa [prefixWord, tailWord_5178248, baseEnd_5178248] using wordTrace_append hprefix tailTrace_5178248
  have hstable : (prefixWord ++ tailWord_5178248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178248).length < 2 ^ (prefixWord ++ tailWord_5178248).sum := by decide
  have hdescent : baseEnd_5178248 < baseStart_5178248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178271 : List Nat := [1, 1, 2, 5, 2, 2, 2, 8]
def baseStart_5178271 : Nat := 118140960795 + 5178271 * 2 ^ 59
def prefixEnd_5178271 : Nat := 4983230072969 + 3 ^ 40 * 5178271 * 2
def baseEnd_5178271 : Nat := 98479332675489434244373

theorem tailTrace_5178271 : CollatzResearch.WordTrace tailWord_5178271 prefixEnd_5178271 98479332675489434244373 := by
  unfold tailWord_5178271
  simp only [CollatzResearch.WordTrace]
  refine ⟨188867059423016020122958667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125911372948677346748639111 188867059423016020122958667)
  ·
    refine ⟨283300589134524030184438001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188867059423016020122958667 283300589134524030184438001)
    ·
      refine ⟨212475441850893022638328501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283300589134524030184438001 212475441850893022638328501)
      ·
        refine ⟨19919572673521220872343297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 212475441850893022638328501 19919572673521220872343297)
        ·
          refine ⟨14939679505140915654257473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19919572673521220872343297 14939679505140915654257473)
          ·
            refine ⟨11204759628855686740693105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14939679505140915654257473 11204759628855686740693105)
            ·
              refine ⟨8403569721641765055519829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11204759628855686740693105 8403569721641765055519829)
              ·
                refine ⟨98479332675489434244373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8403569721641765055519829 98479332675489434244373)
                ·
                  rfl

theorem cell23_5178271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 8].length) (baseStart_5178271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178271 prefixEnd_5178271 := by exact prefixLift 5178271
  have htrace : WordTrace (prefixWord ++ tailWord_5178271) baseStart_5178271 baseEnd_5178271 := by
    simpa [prefixWord, tailWord_5178271, baseEnd_5178271] using wordTrace_append hprefix tailTrace_5178271
  have hstable : (prefixWord ++ tailWord_5178271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178271).length < 2 ^ (prefixWord ++ tailWord_5178271).sum := by decide
  have hdescent : baseEnd_5178271 < baseStart_5178271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178281 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 3]
def baseStart_5178281 : Nat := 118140960795 + 5178281 * 2 ^ 59
def prefixEnd_5178281 : Nat := 4983230072969 + 3 ^ 40 * 5178281 * 2
def baseEnd_5178281 : Nat := 2658947117044759685473025

theorem tailTrace_5178281 : CollatzResearch.WordTrace tailWord_5178281 prefixEnd_5178281 2658947117044759685473025 := by
  unfold tailWord_5178281
  simp only [CollatzResearch.WordTrace]
  refine ⟨188867424152979791830822697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125911616101986527887215131 188867424152979791830822697)
  ·
    refine ⟨141650568114734843873117023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188867424152979791830822697 141650568114734843873117023)
    ·
      refine ⟨212475852172102265809675535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141650568114734843873117023 212475852172102265809675535)
      ·
        refine ⟨318713778258153398714513303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212475852172102265809675535 318713778258153398714513303)
        ·
          refine ⟨478070667387230098071769955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318713778258153398714513303 478070667387230098071769955)
          ·
            refine ⟨717106001080845147107654933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478070667387230098071769955 717106001080845147107654933)
            ·
              refine ⟨33614343800664616270671325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 717106001080845147107654933 33614343800664616270671325)
              ·
                refine ⟨12605378925249231101501747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33614343800664616270671325 12605378925249231101501747)
                ·
                  refine ⟨18908068387873846652252621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12605378925249231101501747 18908068387873846652252621)
                  ·
                    refine ⟨7090525645452692494594733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18908068387873846652252621 7090525645452692494594733)
                    ·
                      refine ⟨2658947117044759685473025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7090525645452692494594733 2658947117044759685473025)
                      ·
                        rfl

theorem cell23_5178281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_5178281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178281 prefixEnd_5178281 := by exact prefixLift 5178281
  have htrace : WordTrace (prefixWord ++ tailWord_5178281) baseStart_5178281 baseEnd_5178281 := by
    simpa [prefixWord, tailWord_5178281, baseEnd_5178281] using wordTrace_append hprefix tailTrace_5178281
  have hstable : (prefixWord ++ tailWord_5178281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178281).length < 2 ^ (prefixWord ++ tailWord_5178281).sum := by decide
  have hdescent : baseEnd_5178281 < baseStart_5178281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178284 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 2, 7]
def baseStart_5178284 : Nat := 118140960795 + 5178284 * 2 ^ 59
def prefixEnd_5178284 : Nat := 4983230072969 + 3 ^ 40 * 5178284 * 2
def baseEnd_5178284 : Nat := 886316219162241057911837

theorem tailTrace_5178284 : CollatzResearch.WordTrace tailWord_5178284 prefixEnd_5178284 886316219162241057911837 := by
  unfold tailWord_5178284
  simp only [CollatzResearch.WordTrace]
  refine ⟨94433766785984461671590953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125911689047979282228787937 94433766785984461671590953)
  ·
    refine ⟨70825325089488346253693215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94433766785984461671590953 70825325089488346253693215)
    ·
      refine ⟨106237987634232519380539823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70825325089488346253693215 106237987634232519380539823)
      ·
        refine ⟨159356981451348779070809735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106237987634232519380539823 159356981451348779070809735)
        ·
          refine ⟨239035472177023168606214603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159356981451348779070809735 239035472177023168606214603)
          ·
            refine ⟨358553208265534752909321905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239035472177023168606214603 358553208265534752909321905)
            ·
              refine ⟨268914906199151064681991429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358553208265534752909321905 268914906199151064681991429)
              ·
                refine ⟨50421544912340824627873393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 268914906199151064681991429 50421544912340824627873393)
                ·
                  refine ⟨37816158684255618470905045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50421544912340824627873393 37816158684255618470905045)
                  ·
                    refine ⟨886316219162241057911837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37816158684255618470905045 886316219162241057911837)
                    ·
                      rfl

theorem cell23_5178284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 7].length) (baseStart_5178284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178284 prefixEnd_5178284 := by exact prefixLift 5178284
  have htrace : WordTrace (prefixWord ++ tailWord_5178284) baseStart_5178284 baseEnd_5178284 := by
    simpa [prefixWord, tailWord_5178284, baseEnd_5178284] using wordTrace_append hprefix tailTrace_5178284
  have hstable : (prefixWord ++ tailWord_5178284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178284).length < 2 ^ (prefixWord ++ tailWord_5178284).sum := by decide
  have hdescent : baseEnd_5178284 < baseStart_5178284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178315 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 3]
def baseStart_5178315 : Nat := 118140960795 + 5178315 * 2 ^ 59
def prefixEnd_5178315 : Nat := 4983230072969 + 3 ^ 40 * 5178315 * 2
def baseEnd_5178315 : Nat := 2658964575387012552447869

theorem tailTrace_5178315 : CollatzResearch.WordTrace tailWord_5178315 prefixEnd_5178315 2658964575387012552447869 := by
  unfold tailWord_5178315
  simp only [CollatzResearch.WordTrace]
  refine ⟨188868664234856615637560399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125912442823237743758373599 188868664234856615637560399)
  ·
    refine ⟨283302996352284923456340599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188868664234856615637560399 283302996352284923456340599)
    ·
      refine ⟨424954494528427385184510899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283302996352284923456340599 424954494528427385184510899)
      ·
        refine ⟨637431741792641077776766349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424954494528427385184510899 637431741792641077776766349)
        ·
          refine ⟨239036903172240404166287381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 637431741792641077776766349 239036903172240404166287381)
          ·
            refine ⟨11204854836198768945294721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 239036903172240404166287381 11204854836198768945294721)
            ·
              refine ⟨8403641127149076708971041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11204854836198768945294721 8403641127149076708971041)
              ·
                refine ⟨6302730845361807531728281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8403641127149076708971041 6302730845361807531728281)
                ·
                  refine ⟨4727048134021355648796211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6302730845361807531728281 4727048134021355648796211)
                  ·
                    refine ⟨7090572201032033473194317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727048134021355648796211 7090572201032033473194317)
                    ·
                      refine ⟨2658964575387012552447869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7090572201032033473194317 2658964575387012552447869)
                      ·
                        rfl

theorem cell23_5178315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 3].length) (baseStart_5178315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178315 prefixEnd_5178315 := by exact prefixLift 5178315
  have htrace : WordTrace (prefixWord ++ tailWord_5178315) baseStart_5178315 baseEnd_5178315 := by
    simpa [prefixWord, tailWord_5178315, baseEnd_5178315] using wordTrace_append hprefix tailTrace_5178315
  have hstable : (prefixWord ++ tailWord_5178315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178315).length < 2 ^ (prefixWord ++ tailWord_5178315).sum := by decide
  have hdescent : baseEnd_5178315 < baseStart_5178315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178366 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_5178366 : Nat := 118140960795 + 5178366 * 2 ^ 59
def prefixEnd_5178366 : Nat := 4983230072969 + 3 ^ 40 * 5178366 * 2
def baseEnd_5178366 : Nat := 2658990762900391852910135

theorem tailTrace_5178366 : CollatzResearch.WordTrace tailWord_5178366 prefixEnd_5178366 2658990762900391852910135 := by
  unfold tailWord_5178366
  simp only [CollatzResearch.WordTrace]
  refine ⟨23608815544708981418458369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125913682905114567565111301 23608815544708981418458369)
  ·
    refine ⟨17706611658531736063843777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23608815544708981418458369 17706611658531736063843777)
    ·
      refine ⟨13279958743898802047882833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17706611658531736063843777 13279958743898802047882833)
      ·
        refine ⟨9959969057924101535912125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13279958743898802047882833 9959969057924101535912125)
        ·
          refine ⟨3734988396721538075967047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9959969057924101535912125 3734988396721538075967047)
          ·
            refine ⟨5602482595082307113950571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3734988396721538075967047 5602482595082307113950571)
            ·
              refine ⟨8403723892623460670925857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5602482595082307113950571 8403723892623460670925857)
              ·
                refine ⟨6302792919467595503194393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8403723892623460670925857 6302792919467595503194393)
                ·
                  refine ⟨4727094689600696627395795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6302792919467595503194393 4727094689600696627395795)
                  ·
                    refine ⟨7090642034401044941093693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727094689600696627395795 7090642034401044941093693)
                    ·
                      refine ⟨2658990762900391852910135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7090642034401044941093693 2658990762900391852910135)
                      ·
                        rfl

theorem cell23_5178366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_5178366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178366 prefixEnd_5178366 := by exact prefixLift 5178366
  have htrace : WordTrace (prefixWord ++ tailWord_5178366) baseStart_5178366 baseEnd_5178366 := by
    simpa [prefixWord, tailWord_5178366, baseEnd_5178366] using wordTrace_append hprefix tailTrace_5178366
  have hstable : (prefixWord ++ tailWord_5178366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178366).length < 2 ^ (prefixWord ++ tailWord_5178366).sum := by decide
  have hdescent : baseEnd_5178366 < baseStart_5178366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178378 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 7]
def baseStart_5178378 : Nat := 118140960795 + 5178378 * 2 ^ 59
def prefixEnd_5178378 : Nat := 4983230072969 + 3 ^ 40 * 5178378 * 2
def baseEnd_5178378 : Nat := 295444102740916200662231

theorem tailTrace_5178378 : CollatzResearch.WordTrace tailWord_5178378 prefixEnd_5178378 295444102740916200662231 := by
  unfold tailWord_5178378
  simp only [CollatzResearch.WordTrace]
  refine ⟨47217740508407094349275947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125913974689085584931402525 47217740508407094349275947)
  ·
    refine ⟨70826610762610641523913921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47217740508407094349275947 70826610762610641523913921)
    ·
      refine ⟨53119958071957981142935441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70826610762610641523913921 53119958071957981142935441)
      ·
        refine ⟨39839968553968485857201581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53119958071957981142935441 39839968553968485857201581)
        ·
          refine ⟨14939988207738182196450593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39839968553968485857201581 14939988207738182196450593)
          ·
            refine ⟨11204991155803636647337945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14939988207738182196450593 11204991155803636647337945)
            ·
              refine ⟨8403743366852727485503459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11204991155803636647337945 8403743366852727485503459)
              ·
                refine ⟨12605615050279091228255189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8403743366852727485503459 12605615050279091228255189)
                ·
                  refine ⟨295444102740916200662231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12605615050279091228255189 295444102740916200662231)
                  ·
                    rfl

theorem cell23_5178378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_5178378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178378 prefixEnd_5178378 := by exact prefixLift 5178378
  have htrace : WordTrace (prefixWord ++ tailWord_5178378) baseStart_5178378 baseEnd_5178378 := by
    simpa [prefixWord, tailWord_5178378, baseEnd_5178378] using wordTrace_append hprefix tailTrace_5178378
  have hstable : (prefixWord ++ tailWord_5178378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178378).length < 2 ^ (prefixWord ++ tailWord_5178378).sum := by decide
  have hdescent : baseEnd_5178378 < baseStart_5178378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178389 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_5178389 : Nat := 118140960795 + 5178389 * 2 ^ 59
def prefixEnd_5178389 : Nat := 4983230072969 + 3 ^ 40 * 5178389 * 2
def baseEnd_5178389 : Nat := 2659002572955445262922529

theorem tailTrace_5178389 : CollatzResearch.WordTrace tailWord_5178389 prefixEnd_5178389 2659002572955445262922529 := by
  unfold tailWord_5178389
  simp only [CollatzResearch.WordTrace]
  refine ⟨188871363236588526275754221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125914242157725684183836147 188871363236588526275754221)
  ·
    refine ⟨70826761213720697353407833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 188871363236588526275754221 70826761213720697353407833)
    ·
      refine ⟨53120070910290523015055875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70826761213720697353407833 53120070910290523015055875)
      ·
        refine ⟨79680106365435784522583813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53120070910290523015055875 79680106365435784522583813)
        ·
          refine ⟨14940019943519209597984465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79680106365435784522583813 14940019943519209597984465)
          ·
            refine ⟨11205014957639407198488349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14940019943519209597984465 11205014957639407198488349)
            ·
              refine ⟨4201880609114777699433131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11205014957639407198488349 4201880609114777699433131)
              ·
                refine ⟨6302820913672166549149697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201880609114777699433131 6302820913672166549149697)
                ·
                  refine ⟨4727115685254124911862273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6302820913672166549149697 4727115685254124911862273)
                  ·
                    refine ⟨3545336763940593683896705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4727115685254124911862273 3545336763940593683896705)
                    ·
                      refine ⟨2659002572955445262922529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545336763940593683896705 2659002572955445262922529)
                      ·
                        rfl

theorem cell23_5178389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_5178389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178389 prefixEnd_5178389 := by exact prefixLift 5178389
  have htrace : WordTrace (prefixWord ++ tailWord_5178389) baseStart_5178389 baseEnd_5178389 := by
    simpa [prefixWord, tailWord_5178389, baseEnd_5178389] using wordTrace_append hprefix tailTrace_5178389
  have hstable : (prefixWord ++ tailWord_5178389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178389).length < 2 ^ (prefixWord ++ tailWord_5178389).sum := by decide
  have hdescent : baseEnd_5178389 < baseStart_5178389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178411 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 4]
def baseStart_5178411 : Nat := 118140960795 + 5178411 * 2 ^ 59
def prefixEnd_5178411 : Nat := 4983230072969 + 3 ^ 40 * 5178411 * 2
def baseEnd_5178411 : Nat := 2659013869529844176847427

theorem tailTrace_5178411 : CollatzResearch.WordTrace tailWord_5178411 prefixEnd_5178411 2659013869529844176847427 := by
  unfold tailWord_5178411
  simp only [CollatzResearch.WordTrace]
  refine ⟨188872165642508824033055087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125914777095005882688703391 188872165642508824033055087)
  ·
    refine ⟨283308248463763236049582631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188872165642508824033055087 283308248463763236049582631)
    ·
      refine ⟨424962372695644854074373947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283308248463763236049582631 424962372695644854074373947)
      ·
        refine ⟨637443559043467281111560921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424962372695644854074373947 637443559043467281111560921)
        ·
          refine ⟨478082669282600460833670691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637443559043467281111560921 478082669282600460833670691)
          ·
            refine ⟨717124003923900691250506037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478082669282600460833670691 717124003923900691250506037)
            ·
              refine ⟨67230375367865689804734941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 717124003923900691250506037 67230375367865689804734941)
              ·
                refine ⟨25211390762949633676775603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67230375367865689804734941 25211390762949633676775603)
                ·
                  refine ⟨37817086144424450515163405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25211390762949633676775603 37817086144424450515163405)
                  ·
                    refine ⟨14181407304159168943186277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37817086144424450515163405 14181407304159168943186277)
                    ·
                      refine ⟨2659013869529844176847427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14181407304159168943186277 2659013869529844176847427)
                      ·
                        rfl

theorem cell23_5178411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 4].length) (baseStart_5178411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178411 prefixEnd_5178411 := by exact prefixLift 5178411
  have htrace : WordTrace (prefixWord ++ tailWord_5178411) baseStart_5178411 baseEnd_5178411 := by
    simpa [prefixWord, tailWord_5178411, baseEnd_5178411] using wordTrace_append hprefix tailTrace_5178411
  have hstable : (prefixWord ++ tailWord_5178411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178411).length < 2 ^ (prefixWord ++ tailWord_5178411).sum := by decide
  have hdescent : baseEnd_5178411 < baseStart_5178411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178428 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_5178428 : Nat := 118140960795 + 5178428 * 2 ^ 59
def prefixEnd_5178428 : Nat := 4983230072969 + 3 ^ 40 * 5178428 * 2
def baseEnd_5178428 : Nat := 2659022598700970610334849

theorem tailTrace_5178428 : CollatzResearch.WordTrace tailWord_5178428 prefixEnd_5178428 2659022598700970610334849 := by
  unfold tailWord_5178428
  simp only [CollatzResearch.WordTrace]
  refine ⟨94436392841723617968211969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125915190455631490624282625 94436392841723617968211969)
  ·
    refine ⟨70827294631292713476158977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94436392841723617968211969 70827294631292713476158977)
    ·
      refine ⟨53120470973469535107119233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70827294631292713476158977 53120470973469535107119233)
      ·
        refine ⟨39840353230102151330339425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53120470973469535107119233 39840353230102151330339425)
        ·
          refine ⟨29880264922576613497754569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39840353230102151330339425 29880264922576613497754569)
          ·
            refine ⟨22410198691932460123315927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29880264922576613497754569 22410198691932460123315927)
            ·
              refine ⟨33615298037898690184973891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22410198691932460123315927 33615298037898690184973891)
              ·
                refine ⟨50422947056848035277460837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33615298037898690184973891 50422947056848035277460837)
                ·
                  refine ⟨9454302573159006614523907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50422947056848035277460837 9454302573159006614523907)
                  ·
                    refine ⟨14181453859738509921785861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9454302573159006614523907 14181453859738509921785861)
                    ·
                      refine ⟨2659022598700970610334849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14181453859738509921785861 2659022598700970610334849)
                      ·
                        rfl

theorem cell23_5178428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_5178428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178428 prefixEnd_5178428 := by exact prefixLift 5178428
  have htrace : WordTrace (prefixWord ++ tailWord_5178428) baseStart_5178428 baseEnd_5178428 := by
    simpa [prefixWord, tailWord_5178428, baseEnd_5178428] using wordTrace_append hprefix tailTrace_5178428
  have hstable : (prefixWord ++ tailWord_5178428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178428).length < 2 ^ (prefixWord ++ tailWord_5178428).sum := by decide
  have hdescent : baseEnd_5178428 < baseStart_5178428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178441 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_5178441 : Nat := 118140960795 + 5178441 * 2 ^ 59
def prefixEnd_5178441 : Nat := 4983230072969 + 3 ^ 40 * 5178441 * 2
def baseEnd_5178441 : Nat := 2659029273949479059472289

theorem tailTrace_5178441 : CollatzResearch.WordTrace tailWord_5178441 prefixEnd_5178441 2659029273949479059472289 := by
  unfold tailWord_5178441
  simp only [CollatzResearch.WordTrace]
  refine ⟨188873259832400139156647177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125915506554933426104431451 188873259832400139156647177)
  ·
    refine ⟨141654944874300104367485383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188873259832400139156647177 141654944874300104367485383)
    ·
      refine ⟨212482417311450156551228075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141654944874300104367485383 212482417311450156551228075)
      ·
        refine ⟨318723625967175234826842113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212482417311450156551228075 318723625967175234826842113)
        ·
          refine ⟨239042719475381426120131585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318723625967175234826842113 239042719475381426120131585)
          ·
            refine ⟨179282039606536069590098689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239042719475381426120131585 179282039606536069590098689)
            ·
              refine ⟨134461529704902052192574017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179282039606536069590098689 134461529704902052192574017)
              ·
                refine ⟨100846147278676539144430513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134461529704902052192574017 100846147278676539144430513)
                ·
                  refine ⟨75634610459007404358322885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100846147278676539144430513 75634610459007404358322885)
                  ·
                    refine ⟨14181489461063888317185541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75634610459007404358322885 14181489461063888317185541)
                    ·
                      refine ⟨2659029273949479059472289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14181489461063888317185541 2659029273949479059472289)
                      ·
                        rfl

theorem cell23_5178441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_5178441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178441 prefixEnd_5178441 := by exact prefixLift 5178441
  have htrace : WordTrace (prefixWord ++ tailWord_5178441) baseStart_5178441 baseEnd_5178441 := by
    simpa [prefixWord, tailWord_5178441, baseEnd_5178441] using wordTrace_append hprefix tailTrace_5178441
  have hstable : (prefixWord ++ tailWord_5178441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178441).length < 2 ^ (prefixWord ++ tailWord_5178441).sum := by decide
  have hdescent : baseEnd_5178441 < baseStart_5178441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178491 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 5]
def baseStart_5178491 : Nat := 118140960795 + 5178491 * 2 ^ 59
def prefixEnd_5178491 : Nat := 4983230072969 + 3 ^ 40 * 5178491 * 2
def baseEnd_5178491 : Nat := 2659054947982203863847059

theorem tailTrace_5178491 : CollatzResearch.WordTrace tailWord_5178491 prefixEnd_5178491 2659054947982203863847059 := by
  unfold tailWord_5178491
  simp only [CollatzResearch.WordTrace]
  refine ⟨188875083482218997695967327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125916722321479331797311551 188875083482218997695967327)
  ·
    refine ⟨283312625223328496543950991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188875083482218997695967327 283312625223328496543950991)
    ·
      refine ⟨424968937834992744815926487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283312625223328496543950991 424968937834992744815926487)
      ·
        refine ⟨637453406752489117223889731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424968937834992744815926487 637453406752489117223889731)
        ·
          refine ⟨956180110128733675835834597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637453406752489117223889731 956180110128733675835834597)
          ·
            refine ⟨179283770649137564219218987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 956180110128733675835834597 179283770649137564219218987)
            ·
              refine ⟨268925655973706346328828481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179283770649137564219218987 268925655973706346328828481)
              ·
                refine ⟨201694241980279759746621361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268925655973706346328828481 201694241980279759746621361)
                ·
                  refine ⟨151270681485209819809966021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201694241980279759746621361 151270681485209819809966021)
                  ·
                    refine ⟨28363252778476841214368629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151270681485209819809966021 28363252778476841214368629)
                    ·
                      refine ⟨2659054947982203863847059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28363252778476841214368629 2659054947982203863847059)
                      ·
                        rfl

theorem cell23_5178491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 5].length) (baseStart_5178491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178491 prefixEnd_5178491 := by exact prefixLift 5178491
  have htrace : WordTrace (prefixWord ++ tailWord_5178491) baseStart_5178491 baseEnd_5178491 := by
    simpa [prefixWord, tailWord_5178491, baseEnd_5178491] using wordTrace_append hprefix tailTrace_5178491
  have hstable : (prefixWord ++ tailWord_5178491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178491).length < 2 ^ (prefixWord ++ tailWord_5178491).sum := by decide
  have hdescent : baseEnd_5178491 < baseStart_5178491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178522 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2]
def baseStart_5178522 : Nat := 118140960795 + 5178522 * 2 ^ 59
def prefixEnd_5178522 : Nat := 4983230072969 + 3 ^ 40 * 5178522 * 2
def baseEnd_5178522 : Nat := 2659070865882493242559417

theorem tailTrace_5178522 : CollatzResearch.WordTrace tailWord_5178522 prefixEnd_5178522 2659070865882493242559417 := by
  unfold tailWord_5178522
  simp only [CollatzResearch.WordTrace]
  refine ⟨47219053536276672497586455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125917476096737793326897213 47219053536276672497586455)
  ·
    refine ⟨70828580304415008746379683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47219053536276672497586455 70828580304415008746379683)
    ·
      refine ⟨106242870456622513119569525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70828580304415008746379683 106242870456622513119569525)
      ·
        refine ⟨9960269105308360604959643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106242870456622513119569525 9960269105308360604959643)
        ·
          refine ⟨14940403657962540907439465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9960269105308360604959643 14940403657962540907439465)
          ·
            refine ⟨11205302743471905680579599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14940403657962540907439465 11205302743471905680579599)
            ·
              refine ⟨16807954115207858520869399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11205302743471905680579599 16807954115207858520869399)
              ·
                refine ⟨25211931172811787781304099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16807954115207858520869399 25211931172811787781304099)
                ·
                  refine ⟨37817896759217681671956149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25211931172811787781304099 37817896759217681671956149)
                  ·
                    refine ⟨3545427821176657656745889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37817896759217681671956149 3545427821176657656745889)
                    ·
                      refine ⟨2659070865882493242559417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545427821176657656745889 2659070865882493242559417)
                      ·
                        rfl

theorem cell23_5178522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_5178522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178522 prefixEnd_5178522 := by exact prefixLift 5178522
  have htrace : WordTrace (prefixWord ++ tailWord_5178522) baseStart_5178522 baseEnd_5178522 := by
    simpa [prefixWord, tailWord_5178522, baseEnd_5178522] using wordTrace_append hprefix tailTrace_5178522
  have hstable : (prefixWord ++ tailWord_5178522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178522).length < 2 ^ (prefixWord ++ tailWord_5178522).sum := by decide
  have hdescent : baseEnd_5178522 < baseStart_5178522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178528 : List Nat := [2, 1, 1, 4, 2, 1, 1, 4, 1, 6]
def baseStart_5178528 : Nat := 118140960795 + 5178528 * 2 ^ 59
def prefixEnd_5178528 : Nat := 4983230072969 + 3 ^ 40 * 5178528 * 2
def baseEnd_5178528 : Nat := 886357982255473406361463

theorem tailTrace_5178528 : CollatzResearch.WordTrace tailWord_5178528 prefixEnd_5178528 886357982255473406361463 := by
  unfold tailWord_5178528
  simp only [CollatzResearch.WordTrace]
  refine ⟨94438216491542476507532119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125917621988723302010042825 94438216491542476507532119)
  ·
    refine ⟨141657324737313714761298179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94438216491542476507532119 141657324737313714761298179)
    ·
      refine ⟨212485987105970572141947269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141657324737313714761298179 212485987105970572141947269)
      ·
        refine ⟨39841122582369482276615113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 212485987105970572141947269 39841122582369482276615113)
        ·
          refine ⟨29880841936777111707461335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39841122582369482276615113 29880841936777111707461335)
          ·
            refine ⟨44821262905165667561192003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29880841936777111707461335 44821262905165667561192003)
            ·
              refine ⟨67231894357748501341788005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44821262905165667561192003 67231894357748501341788005)
              ·
                refine ⟨12605980192077844001585251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67231894357748501341788005 12605980192077844001585251)
                ·
                  refine ⟨18908970288116766002377877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12605980192077844001585251 18908970288116766002377877)
                  ·
                    refine ⟨886357982255473406361463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18908970288116766002377877 886357982255473406361463)
                    ·
                      rfl

theorem cell23_5178528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 1, 6].length) (baseStart_5178528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178528 prefixEnd_5178528 := by exact prefixLift 5178528
  have htrace : WordTrace (prefixWord ++ tailWord_5178528) baseStart_5178528 baseEnd_5178528 := by
    simpa [prefixWord, tailWord_5178528, baseEnd_5178528] using wordTrace_append hprefix tailTrace_5178528
  have hstable : (prefixWord ++ tailWord_5178528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178528).length < 2 ^ (prefixWord ++ tailWord_5178528).sum := by decide
  have hdescent : baseEnd_5178528 < baseStart_5178528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178529 : List Nat := [1, 2, 3, 3, 1, 1, 4, 3, 1, 1, 3]
def baseStart_5178529 : Nat := 118140960795 + 5178529 * 2 ^ 59
def prefixEnd_5178529 : Nat := 4983230072969 + 3 ^ 40 * 5178529 * 2
def baseEnd_5178529 : Nat := 2659074460247074715171885

theorem tailTrace_5178529 : CollatzResearch.WordTrace tailWord_5178529 prefixEnd_5178529 2659074460247074715171885 := by
  unfold tailWord_5178529
  simp only [CollatzResearch.WordTrace]
  refine ⟨188876469456081330185850641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125917646304054220123900427 188876469456081330185850641)
  ·
    refine ⟨141657352092060997639387981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188876469456081330185850641 141657352092060997639387981)
    ·
      refine ⟨53121507034522874114770493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 141657352092060997639387981 53121507034522874114770493)
      ·
        refine ⟨19920565137946077793038935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53121507034522874114770493 19920565137946077793038935)
        ·
          refine ⟨29880847706919116689558403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19920565137946077793038935 29880847706919116689558403)
          ·
            refine ⟨44821271560378675034337605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29880847706919116689558403 44821271560378675034337605)
            ·
              refine ⟨8403988417571001568938301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44821271560378675034337605 8403988417571001568938301)
              ·
                refine ⟨3151495656589125588351863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8403988417571001568938301 3151495656589125588351863)
                ·
                  refine ⟨4727243484883688382527795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151495656589125588351863 4727243484883688382527795)
                  ·
                    refine ⟨7090865227325532573791693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727243484883688382527795 7090865227325532573791693)
                    ·
                      refine ⟨2659074460247074715171885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7090865227325532573791693 2659074460247074715171885)
                      ·
                        rfl

theorem cell23_5178529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_5178529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178529 prefixEnd_5178529 := by exact prefixLift 5178529
  have htrace : WordTrace (prefixWord ++ tailWord_5178529) baseStart_5178529 baseEnd_5178529 := by
    simpa [prefixWord, tailWord_5178529, baseEnd_5178529] using wordTrace_append hprefix tailTrace_5178529
  have hstable : (prefixWord ++ tailWord_5178529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178529).length < 2 ^ (prefixWord ++ tailWord_5178529).sum := by decide
  have hdescent : baseEnd_5178529 < baseStart_5178529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178532 : List Nat := [2, 3, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_5178532 : Nat := 118140960795 + 5178532 * 2 ^ 59
def prefixEnd_5178532 : Nat := 4983230072969 + 3 ^ 40 * 5178532 * 2
def baseEnd_5178532 : Nat := 886358666896346067811457

theorem tailTrace_5178532 : CollatzResearch.WordTrace tailWord_5178532 prefixEnd_5178532 886358666896346067811457 := by
  unfold tailWord_5178532
  simp only [CollatzResearch.WordTrace]
  refine ⟨94438289437535230849104925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125917719250046974465473233 94438289437535230849104925)
  ·
    refine ⟨35414358539075711568414347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 94438289437535230849104925 35414358539075711568414347)
    ·
      refine ⟨53121537808613567352621521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35414358539075711568414347 53121537808613567352621521)
      ·
        refine ⟨39841153356460175514466141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53121537808613567352621521 39841153356460175514466141)
        ·
          refine ⟨14940432508672565817924803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39841153356460175514466141 14940432508672565817924803)
          ·
            refine ⟨22410648763008848726887205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14940432508672565817924803 22410648763008848726887205)
            ·
              refine ⟨4201996643064159136291351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22410648763008848726887205 4201996643064159136291351)
              ·
                refine ⟨6302994964596238704437027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4201996643064159136291351 6302994964596238704437027)
                ·
                  refine ⟨9454492446894358056655541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6302994964596238704437027 9454492446894358056655541)
                  ·
                    refine ⟨886358666896346067811457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9454492446894358056655541 886358666896346067811457)
                    ·
                      rfl

theorem cell23_5178532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_5178532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178532 prefixEnd_5178532 := by exact prefixLift 5178532
  have htrace : WordTrace (prefixWord ++ tailWord_5178532) baseStart_5178532 baseEnd_5178532 := by
    simpa [prefixWord, tailWord_5178532, baseEnd_5178532] using wordTrace_append hprefix tailTrace_5178532
  have hstable : (prefixWord ++ tailWord_5178532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178532).length < 2 ^ (prefixWord ++ tailWord_5178532).sum := by decide
  have hdescent : baseEnd_5178532 < baseStart_5178532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178580 : List Nat := [2, 4, 1, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5178580 : Nat := 118140960795 + 5178580 * 2 ^ 59
def prefixEnd_5178580 : Nat := 4983230072969 + 3 ^ 40 * 5178580 * 2
def baseEnd_5178580 : Nat := 2659100647760454015634151

theorem tailTrace_5178580 : CollatzResearch.WordTrace tailWord_5178580 prefixEnd_5178580 2659100647760454015634151 := by
  unfold tailWord_5178580
  simp only [CollatzResearch.WordTrace]
  refine ⟨94439164789448282947978597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125918886385931043930638129 94439164789448282947978597)
  ·
    refine ⟨17707343398021553052745987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94439164789448282947978597 17707343398021553052745987)
    ·
      refine ⟨26561015097032329579118981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17707343398021553052745987 26561015097032329579118981)
      ·
        refine ⟨4980190330693561796084809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26561015097032329579118981 4980190330693561796084809)
        ·
          refine ⟨3735142748020171347063607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4980190330693561796084809 3735142748020171347063607)
          ·
            refine ⟨5602714122030257020595411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735142748020171347063607 5602714122030257020595411)
            ·
              refine ⟨8404071183045385530893117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5602714122030257020595411 8404071183045385530893117)
              ·
                refine ⟨3151526693642019574084919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8404071183045385530893117 3151526693642019574084919)
                ·
                  refine ⟨4727290040463029361127379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151526693642019574084919 4727290040463029361127379)
                  ·
                    refine ⟨7090935060694544041691069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727290040463029361127379 7090935060694544041691069)
                    ·
                      refine ⟨2659100647760454015634151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7090935060694544041691069 2659100647760454015634151)
                      ·
                        rfl

theorem cell23_5178580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5178580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178580 prefixEnd_5178580 := by exact prefixLift 5178580
  have htrace : WordTrace (prefixWord ++ tailWord_5178580) baseStart_5178580 baseEnd_5178580 := by
    simpa [prefixWord, tailWord_5178580, baseEnd_5178580] using wordTrace_append hprefix tailTrace_5178580
  have hstable : (prefixWord ++ tailWord_5178580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178580).length < 2 ^ (prefixWord ++ tailWord_5178580).sum := by decide
  have hdescent : baseEnd_5178580 < baseStart_5178580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178602 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_5178602 : Nat := 118140960795 + 5178602 * 2 ^ 59
def prefixEnd_5178602 : Nat := 4983230072969 + 3 ^ 40 * 5178602 * 2
def baseEnd_5178602 : Nat := 2659111944334852929559049

theorem tailTrace_5178602 : CollatzResearch.WordTrace tailWord_5178602 prefixEnd_5178602 2659111944334852929559049 := by
  unfold tailWord_5178602
  simp only [CollatzResearch.WordTrace]
  refine ⟨47219782996204215913314515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125919421323211242435505373 47219782996204215913314515)
  ·
    refine ⟨70829674494306323869971773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47219782996204215913314515 70829674494306323869971773)
    ·
      refine ⟨26561127935364871451239415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70829674494306323869971773 26561127935364871451239415)
      ·
        refine ⟨39841691903047307176859123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26561127935364871451239415 39841691903047307176859123)
        ·
          refine ⟨59762537854570960765288685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39841691903047307176859123 59762537854570960765288685)
          ·
            refine ⟨22410951695464110286983257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59762537854570960765288685 22410951695464110286983257)
            ·
              refine ⟨16808213771598082715237443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22410951695464110286983257 16808213771598082715237443)
              ·
                refine ⟨25212320657397124072856165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16808213771598082715237443 25212320657397124072856165)
                ·
                  refine ⟨4727310123261960763660531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25212320657397124072856165 4727310123261960763660531)
                  ·
                    refine ⟨7090965184892941145490797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4727310123261960763660531 7090965184892941145490797)
                    ·
                      refine ⟨2659111944334852929559049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7090965184892941145490797 2659111944334852929559049)
                      ·
                        rfl

theorem cell23_5178602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_5178602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178602 prefixEnd_5178602 := by exact prefixLift 5178602
  have htrace : WordTrace (prefixWord ++ tailWord_5178602) baseStart_5178602 baseEnd_5178602 := by
    simpa [prefixWord, tailWord_5178602, baseEnd_5178602] using wordTrace_append hprefix tailTrace_5178602
  have hstable : (prefixWord ++ tailWord_5178602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178602).length < 2 ^ (prefixWord ++ tailWord_5178602).sum := by decide
  have hdescent : baseEnd_5178602 < baseStart_5178602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178618 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_5178618 : Nat := 118140960795 + 5178618 * 2 ^ 59
def prefixEnd_5178618 : Nat := 4983230072969 + 3 ^ 40 * 5178618 * 2
def baseEnd_5178618 : Nat := 886373386675108288986325

theorem tailTrace_5178618 : CollatzResearch.WordTrace tailWord_5178618 prefixEnd_5178618 886373386675108288986325 := by
  unfold tailWord_5178618
  simp only [CollatzResearch.WordTrace]
  refine ⟨47219928888189724596460127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125919810368505932257227005 47219928888189724596460127)
  ·
    refine ⟨70829893332284586894690191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47219928888189724596460127 70829893332284586894690191)
    ·
      refine ⟨106244839998426880342035287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70829893332284586894690191 106244839998426880342035287)
      ·
        refine ⟨159367259997640320513052931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106244839998426880342035287 159367259997640320513052931)
        ·
          refine ⟨239050889996460480769579397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159367259997640320513052931 239050889996460480769579397)
          ·
            refine ⟨44822041874336340144296137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 239050889996460480769579397 44822041874336340144296137)
            ·
              refine ⟨33616531405752255108222103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44822041874336340144296137 33616531405752255108222103)
              ·
                refine ⟨50424797108628382662333155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33616531405752255108222103 50424797108628382662333155)
                ·
                  refine ⟨75637195662942573993499733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50424797108628382662333155 75637195662942573993499733)
                  ·
                    refine ⟨886373386675108288986325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75637195662942573993499733 886373386675108288986325)
                    ·
                      rfl

theorem cell23_5178618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_5178618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178618 prefixEnd_5178618 := by exact prefixLift 5178618
  have htrace : WordTrace (prefixWord ++ tailWord_5178618) baseStart_5178618 baseEnd_5178618 := by
    simpa [prefixWord, tailWord_5178618, baseEnd_5178618] using wordTrace_append hprefix tailTrace_5178618
  have hstable : (prefixWord ++ tailWord_5178618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178618).length < 2 ^ (prefixWord ++ tailWord_5178618).sum := by decide
  have hdescent : baseEnd_5178618 < baseStart_5178618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178654 : List Nat := [4, 3, 2, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5178654 : Nat := 118140960795 + 5178654 * 2 ^ 59
def prefixEnd_5178654 : Nat := 4983230072969 + 3 ^ 40 * 5178654 * 2
def baseEnd_5178654 : Nat := 2659138645328886726108811

theorem tailTrace_5178654 : CollatzResearch.WordTrace tailWord_5178654 prefixEnd_5178654 2659138645328886726108811 := by
  unfold tailWord_5178654
  simp only [CollatzResearch.WordTrace]
  refine ⟨23610128572578559566768877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125920685720418984356100677 23610128572578559566768877)
  ·
    refine ⟨8853798214716959837538329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23610128572578559566768877 8853798214716959837538329)
    ·
      refine ⟨6640348661037719878153747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8853798214716959837538329 6640348661037719878153747)
      ·
        refine ⟨9960522991556579817230621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6640348661037719878153747 9960522991556579817230621)
        ·
          refine ⟨3735196121833717431461483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9960522991556579817230621 3735196121833717431461483)
          ·
            refine ⟨5602794182750576147192225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735196121833717431461483 5602794182750576147192225)
            ·
              refine ⟨4202095637062932110394169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5602794182750576147192225 4202095637062932110394169)
              ·
                refine ⟨3151571727797199082795627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4202095637062932110394169 3151571727797199082795627)
                ·
                  refine ⟨4727357591695798624193441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3151571727797199082795627 4727357591695798624193441)
                  ·
                    refine ⟨3545518193771848968145081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4727357591695798624193441 3545518193771848968145081)
                    ·
                      refine ⟨2659138645328886726108811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545518193771848968145081 2659138645328886726108811)
                      ·
                        rfl

theorem cell23_5178654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5178654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178654 prefixEnd_5178654 := by exact prefixLift 5178654
  have htrace : WordTrace (prefixWord ++ tailWord_5178654) baseStart_5178654 baseEnd_5178654 := by
    simpa [prefixWord, tailWord_5178654, baseEnd_5178654] using wordTrace_append hprefix tailTrace_5178654
  have hstable : (prefixWord ++ tailWord_5178654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178654).length < 2 ^ (prefixWord ++ tailWord_5178654).sum := by decide
  have hdescent : baseEnd_5178654 < baseStart_5178654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178659 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 2, 2, 2]
def baseStart_5178659 : Nat := 118140960795 + 5178659 * 2 ^ 59
def prefixEnd_5178659 : Nat := 4983230072969 + 3 ^ 40 * 5178659 * 2
def baseEnd_5178659 : Nat := 2659141212732159206546287

theorem tailTrace_5178659 : CollatzResearch.WordTrace tailWord_5178659 prefixEnd_5178659 2659141212732159206546287 := by
  unfold tailWord_5178659
  simp only [CollatzResearch.WordTrace]
  refine ⟨188881210945610362388083031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125920807297073574925388687 188881210945610362388083031)
  ·
    refine ⟨283321816418415543582124547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188881210945610362388083031 283321816418415543582124547)
    ·
      refine ⟨424982724627623315373186821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283321816418415543582124547 424982724627623315373186821)
      ·
        refine ⟨79684260867679371632472529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 424982724627623315373186821 79684260867679371632472529)
        ·
          refine ⟨59763195650759528724354397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79684260867679371632472529 59763195650759528724354397)
          ·
            refine ⟨22411198369034823271632899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59763195650759528724354397 22411198369034823271632899)
            ·
              refine ⟨33616797553552234907449349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22411198369034823271632899 33616797553552234907449349)
              ·
                refine ⟨6303149541291044045146753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33616797553552234907449349 6303149541291044045146753)
                ·
                  refine ⟨4727362155968283033860065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303149541291044045146753 4727362155968283033860065)
                  ·
                    refine ⟨3545521616976212275395049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4727362155968283033860065 3545521616976212275395049)
                    ·
                      refine ⟨2659141212732159206546287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545521616976212275395049 2659141212732159206546287)
                      ·
                        rfl

theorem cell23_5178659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_5178659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178659 prefixEnd_5178659 := by exact prefixLift 5178659
  have htrace : WordTrace (prefixWord ++ tailWord_5178659) baseStart_5178659 baseEnd_5178659 := by
    simpa [prefixWord, tailWord_5178659, baseEnd_5178659] using wordTrace_append hprefix tailTrace_5178659
  have hstable : (prefixWord ++ tailWord_5178659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178659).length < 2 ^ (prefixWord ++ tailWord_5178659).sum := by decide
  have hdescent : baseEnd_5178659 < baseStart_5178659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178668 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 8]
def baseStart_5178668 : Nat := 118140960795 + 5178668 * 2 ^ 59
def prefixEnd_5178668 : Nat := 4983230072969 + 3 ^ 40 * 5178668 * 2
def baseEnd_5178668 : Nat := 2659145834058049671333745

theorem tailTrace_5178668 : CollatzResearch.WordTrace tailWord_5178668 prefixEnd_5178668 2659145834058049671333745 := by
  unfold tailWord_5178668
  simp only [CollatzResearch.WordTrace]
  refine ⟨94440769601288878462580329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125921026135051837950107105 94440769601288878462580329)
  ·
    refine ⟨70830577200966658846935247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 94440769601288878462580329 70830577200966658846935247)
    ·
      refine ⟨106245865801449988270402871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70830577200966658846935247 106245865801449988270402871)
      ·
        refine ⟨159368798702174982405604307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106245865801449988270402871 159368798702174982405604307)
        ·
          refine ⟨239053198053262473608406461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159368798702174982405604307 239053198053262473608406461)
          ·
            refine ⟨89644949269973427603152423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239053198053262473608406461 89644949269973427603152423)
            ·
              refine ⟨134467423904960141404728635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89644949269973427603152423 134467423904960141404728635)
              ·
                refine ⟨201701135857440212107092953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134467423904960141404728635 201701135857440212107092953)
                ·
                  refine ⟨151275851893080159080319715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201701135857440212107092953 151275851893080159080319715)
                  ·
                    refine ⟨226913777839620238620479573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 151275851893080159080319715 226913777839620238620479573)
                    ·
                      refine ⟨2659145834058049671333745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 226913777839620238620479573 2659145834058049671333745)
                      ·
                        rfl

theorem cell23_5178668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_5178668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178668 prefixEnd_5178668 := by exact prefixLift 5178668
  have htrace : WordTrace (prefixWord ++ tailWord_5178668) baseStart_5178668 baseEnd_5178668 := by
    simpa [prefixWord, tailWord_5178668, baseEnd_5178668] using wordTrace_append hprefix tailTrace_5178668
  have hstable : (prefixWord ++ tailWord_5178668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178668).length < 2 ^ (prefixWord ++ tailWord_5178668).sum := by decide
  have hdescent : baseEnd_5178668 < baseStart_5178668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178675 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 3]
def baseStart_5178675 : Nat := 118140960795 + 5178675 * 2 ^ 59
def prefixEnd_5178675 : Nat := 4983230072969 + 3 ^ 40 * 5178675 * 2
def baseEnd_5178675 : Nat := 2659149428422631143946213

theorem tailTrace_5178675 : CollatzResearch.WordTrace tailWord_5178675 prefixEnd_5178675 2659149428422631143946213 := by
  unfold tailWord_5178675
  simp only [CollatzResearch.WordTrace]
  refine ⟨188881794513552397120665479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125921196342368264747110319 188881794513552397120665479)
  ·
    refine ⟨283322691770328595680998219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188881794513552397120665479 283322691770328595680998219)
    ·
      refine ⟨424984037655492893521497329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283322691770328595680998219 424984037655492893521497329)
      ·
        refine ⟨318738028241619670141122997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424984037655492893521497329 318738028241619670141122997)
        ·
          refine ⟨29881690147651844075730281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 318738028241619670141122997 29881690147651844075730281)
          ·
            refine ⟨22411267610738883056797711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29881690147651844075730281 22411267610738883056797711)
            ·
              refine ⟨33616901416108324585196567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22411267610738883056797711 33616901416108324585196567)
              ·
                refine ⟨50425352124162486877794851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33616901416108324585196567 50425352124162486877794851)
                ·
                  refine ⟨75638028186243730316692277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50425352124162486877794851 75638028186243730316692277)
                  ·
                    refine ⟨7091065142460349717189901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75638028186243730316692277 7091065142460349717189901)
                    ·
                      refine ⟨2659149428422631143946213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7091065142460349717189901 2659149428422631143946213)
                      ·
                        rfl

theorem cell23_5178675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_5178675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178675 prefixEnd_5178675 := by exact prefixLift 5178675
  have htrace : WordTrace (prefixWord ++ tailWord_5178675) baseStart_5178675 baseEnd_5178675 := by
    simpa [prefixWord, tailWord_5178675, baseEnd_5178675] using wordTrace_append hprefix tailTrace_5178675
  have hstable : (prefixWord ++ tailWord_5178675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178675).length < 2 ^ (prefixWord ++ tailWord_5178675).sum := by decide
  have hdescent : baseEnd_5178675 < baseStart_5178675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178676 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_5178676 : Nat := 118140960795 + 5178676 * 2 ^ 59
def prefixEnd_5178676 : Nat := 4983230072969 + 3 ^ 40 * 5178676 * 2
def baseEnd_5178676 : Nat := 2659149941903285640033709

theorem tailTrace_5178676 : CollatzResearch.WordTrace tailWord_5178676 prefixEnd_5178676 2659149941903285640033709 := by
  unfold tailWord_5178676
  simp only [CollatzResearch.WordTrace]
  refine ⟨94440915493274387145725941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125921220657699182860967921 94440915493274387145725941)
  ·
    refine ⟨8853835827494473794911807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 94440915493274387145725941 8853835827494473794911807)
    ·
      refine ⟨13280753741241710692367711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8853835827494473794911807 13280753741241710692367711)
      ·
        refine ⟨19921130611862566038551567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13280753741241710692367711 19921130611862566038551567)
        ·
          refine ⟨29881695917793849057827351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19921130611862566038551567 29881695917793849057827351)
          ·
            refine ⟨44822543876690773586741027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29881695917793849057827351 44822543876690773586741027)
            ·
              refine ⟨67233815815036160380111541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44822543876690773586741027 67233815815036160380111541)
              ·
                refine ⟨6303170232659640035635457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67233815815036160380111541 6303170232659640035635457)
                ·
                  refine ⟨4727377674494730026726593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6303170232659640035635457 4727377674494730026726593)
                  ·
                    refine ⟨3545533255871047520044945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4727377674494730026726593 3545533255871047520044945)
                    ·
                      refine ⟨2659149941903285640033709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3545533255871047520044945 2659149941903285640033709)
                      ·
                        rfl

theorem cell23_5178676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_5178676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178676 prefixEnd_5178676 := by exact prefixLift 5178676
  have htrace : WordTrace (prefixWord ++ tailWord_5178676) baseStart_5178676 baseEnd_5178676 := by
    simpa [prefixWord, tailWord_5178676, baseEnd_5178676] using wordTrace_append hprefix tailTrace_5178676
  have hstable : (prefixWord ++ tailWord_5178676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178676).length < 2 ^ (prefixWord ++ tailWord_5178676).sum := by decide
  have hdescent : baseEnd_5178676 < baseStart_5178676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178695 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 1, 7]
def baseStart_5178695 : Nat := 118140960795 + 5178695 * 2 ^ 59
def prefixEnd_5178695 : Nat := 4983230072969 + 3 ^ 40 * 5178695 * 2
def baseEnd_5178695 : Nat := 886386566011907021898707

theorem tailTrace_5178695 : CollatzResearch.WordTrace tailWord_5178695 prefixEnd_5178695 886386566011907021898707 := by
  unfold tailWord_5178695
  simp only [CollatzResearch.WordTrace]
  refine ⟨188882523973479940536393539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125921682648986627024262359 188882523973479940536393539)
  ·
    refine ⟨283323785960219910804590309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188882523973479940536393539 283323785960219910804590309)
    ·
      refine ⟨53123209867541233275860683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 283323785960219910804590309 53123209867541233275860683)
      ·
        refine ⟨79684814801311849913791025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53123209867541233275860683 79684814801311849913791025)
        ·
          refine ⟨59763611100983887435343269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79684814801311849913791025 59763611100983887435343269)
          ·
            refine ⟨11205677081434478894126863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59763611100983887435343269 11205677081434478894126863)
            ·
              refine ⟨16808515622151718341190295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11205677081434478894126863 16808515622151718341190295)
              ·
                refine ⟨25212773433227577511785443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16808515622151718341190295 25212773433227577511785443)
                ·
                  refine ⟨37819160149841366267678165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25212773433227577511785443 37819160149841366267678165)
                  ·
                    refine ⟨886386566011907021898707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37819160149841366267678165 886386566011907021898707)
                    ·
                      rfl

theorem cell23_5178695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_5178695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178695 prefixEnd_5178695 := by exact prefixLift 5178695
  have htrace : WordTrace (prefixWord ++ tailWord_5178695) baseStart_5178695 baseEnd_5178695 := by
    simpa [prefixWord, tailWord_5178695, baseEnd_5178695] using wordTrace_append hprefix tailTrace_5178695
  have hstable : (prefixWord ++ tailWord_5178695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178695).length < 2 ^ (prefixWord ++ tailWord_5178695).sum := by decide
  have hdescent : baseEnd_5178695 < baseStart_5178695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178735 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 3]
def baseStart_5178735 : Nat := 118140960795 + 5178735 * 2 ^ 59
def prefixEnd_5178735 : Nat := 4983230072969 + 3 ^ 40 * 5178735 * 2
def baseEnd_5178735 : Nat := 2659180237261900909195937

theorem tailTrace_5178735 : CollatzResearch.WordTrace tailWord_5178735 prefixEnd_5178735 2659180237261900909195937 := by
  unfold tailWord_5178735
  simp only [CollatzResearch.WordTrace]
  refine ⟨188883982893335027367849659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125922655262223351578566439 188883982893335027367849659)
  ·
    refine ⟨283325974340002541051774489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188883982893335027367849659 283325974340002541051774489)
    ·
      refine ⟨212494480755001905788830867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283325974340002541051774489 212494480755001905788830867)
      ·
        refine ⟨318741721132502858683246301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212494480755001905788830867 318741721132502858683246301)
        ·
          refine ⟨119528145424688572006217363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 318741721132502858683246301 119528145424688572006217363)
          ·
            refine ⟨179292218137032858009326045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119528145424688572006217363 179292218137032858009326045)
            ·
              refine ⟨67234581801387321753497267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179292218137032858009326045 67234581801387321753497267)
              ·
                refine ⟨100851872702080982630245901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67234581801387321753497267 100851872702080982630245901)
                ·
                  refine ⟨37819452263280368486342213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100851872702080982630245901 37819452263280368486342213)
                  ·
                    refine ⟨7091147299365069091189165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37819452263280368486342213 7091147299365069091189165)
                    ·
                      refine ⟨2659180237261900909195937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7091147299365069091189165 2659180237261900909195937)
                      ·
                        rfl

theorem cell23_5178735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_5178735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178735 prefixEnd_5178735 := by exact prefixLift 5178735
  have htrace : WordTrace (prefixWord ++ tailWord_5178735) baseStart_5178735 baseEnd_5178735 := by
    simpa [prefixWord, tailWord_5178735, baseEnd_5178735] using wordTrace_append hprefix tailTrace_5178735
  have hstable : (prefixWord ++ tailWord_5178735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178735).length < 2 ^ (prefixWord ++ tailWord_5178735).sum := by decide
  have hdescent : baseEnd_5178735 < baseStart_5178735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178750 : List Nat := [4, 2, 3, 2, 2, 1, 1, 3, 5]
def baseStart_5178750 : Nat := 118140960795 + 5178750 * 2 ^ 59
def prefixEnd_5178750 : Nat := 4983230072969 + 3 ^ 40 * 5178750 * 2
def baseEnd_5178750 : Nat := 295465326607968705612041

theorem tailTrace_5178750 : CollatzResearch.WordTrace tailWord_5178750 prefixEnd_5178750 295465326607968705612041 := by
  unfold tailWord_5178750
  simp only [CollatzResearch.WordTrace]
  refine ⟨23610566248535085616205713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125923019992187123286430469 23610566248535085616205713)
  ·
    refine ⟨17707924686401314212154285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23610566248535085616205713 17707924686401314212154285)
    ·
      refine ⟨6640471757400492829557857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17707924686401314212154285 6640471757400492829557857)
      ·
        refine ⟨4980353818050369622168393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6640471757400492829557857 4980353818050369622168393)
        ·
          refine ⟨3735265363537777216626295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4980353818050369622168393 3735265363537777216626295)
          ·
            refine ⟨5602898045306665824939443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735265363537777216626295 5602898045306665824939443)
            ·
              refine ⟨8404347067959998737409165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5602898045306665824939443 8404347067959998737409165)
              ·
                refine ⟨3151630150484999526528437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8404347067959998737409165 3151630150484999526528437)
                ·
                  refine ⟨295465326607968705612041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3151630150484999526528437 295465326607968705612041)
                  ·
                    rfl

theorem cell23_5178750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_5178750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178750 prefixEnd_5178750 := by exact prefixLift 5178750
  have htrace : WordTrace (prefixWord ++ tailWord_5178750) baseStart_5178750 baseEnd_5178750 := by
    simpa [prefixWord, tailWord_5178750, baseEnd_5178750] using wordTrace_append hprefix tailTrace_5178750
  have hstable : (prefixWord ++ tailWord_5178750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178750).length < 2 ^ (prefixWord ++ tailWord_5178750).sum := by decide
  have hdescent : baseEnd_5178750 < baseStart_5178750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178755 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 8]
def baseStart_5178755 : Nat := 118140960795 + 5178755 * 2 ^ 59
def prefixEnd_5178755 : Nat := 4983230072969 + 3 ^ 40 * 5178755 * 2
def baseEnd_5178755 : Nat := 295465611874998981216205

theorem tailTrace_5178755 : CollatzResearch.WordTrace tailWord_5178755 prefixEnd_5178755 295465611874998981216205 := by
  unfold tailWord_5178755
  simp only [CollatzResearch.WordTrace]
  refine ⟨188884712353262570783577719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125923141568841713855718479 188884712353262570783577719)
  ·
    refine ⟨283327068529893856175366579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188884712353262570783577719 283327068529893856175366579)
    ·
      refine ⟨424990602794840784263049869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283327068529893856175366579 424990602794840784263049869)
      ·
        refine ⟨159371476048065294098643701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424990602794840784263049869 159371476048065294098643701)
        ·
          refine ⟨14941075879506121321747847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 159371476048065294098643701 14941075879506121321747847)
          ·
            refine ⟨22411613819259181982621771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14941075879506121321747847 22411613819259181982621771)
            ·
              refine ⟨33617420728888772973932657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22411613819259181982621771 33617420728888772973932657)
              ·
                refine ⟨25213065546666579730449493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33617420728888772973932657 25213065546666579730449493)
                ·
                  refine ⟨295465611874998981216205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25213065546666579730449493 295465611874998981216205)
                  ·
                    rfl

theorem cell23_5178755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 8].length) (baseStart_5178755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178755 prefixEnd_5178755 := by exact prefixLift 5178755
  have htrace : WordTrace (prefixWord ++ tailWord_5178755) baseStart_5178755 baseEnd_5178755 := by
    simpa [prefixWord, tailWord_5178755, baseEnd_5178755] using wordTrace_append hprefix tailTrace_5178755
  have hstable : (prefixWord ++ tailWord_5178755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178755).length < 2 ^ (prefixWord ++ tailWord_5178755).sum := by decide
  have hdescent : baseEnd_5178755 < baseStart_5178755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178772 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 8]
def baseStart_5178772 : Nat := 118140960795 + 5178772 * 2 ^ 59
def prefixEnd_5178772 : Nat := 4983230072969 + 3 ^ 40 * 5178772 * 2
def baseEnd_5178772 : Nat := 295466581782901918270363

theorem tailTrace_5178772 : CollatzResearch.WordTrace tailWord_5178772 prefixEnd_5178772 295466581782901918270363 := by
  unfold tailWord_5178772
  simp only [CollatzResearch.WordTrace]
  refine ⟨94442666197100491343473285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125923554929467321791297713 94442666197100491343473285)
  ·
    refine ⟨17707999911956342126901241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 94442666197100491343473285 17707999911956342126901241)
    ·
      refine ⟨13280999933967256595175931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17707999911956342126901241 13280999933967256595175931)
      ·
        refine ⟨19921499900950884892763897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13280999933967256595175931 19921499900950884892763897)
        ·
          refine ⟨14941124925713163669572923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19921499900950884892763897 14941124925713163669572923)
          ·
            refine ⟨22411687388569745504359385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14941124925713163669572923 22411687388569745504359385)
            ·
              refine ⟨16808765541427309128269539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22411687388569745504359385 16808765541427309128269539)
              ·
                refine ⟨25213148312140963692404309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16808765541427309128269539 25213148312140963692404309)
                ·
                  refine ⟨295466581782901918270363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25213148312140963692404309 295466581782901918270363)
                  ·
                    rfl

theorem cell23_5178772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_5178772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178772 prefixEnd_5178772 := by exact prefixLift 5178772
  have htrace : WordTrace (prefixWord ++ tailWord_5178772) baseStart_5178772 baseEnd_5178772 := by
    simpa [prefixWord, tailWord_5178772, baseEnd_5178772] using wordTrace_append hprefix tailTrace_5178772
  have hstable : (prefixWord ++ tailWord_5178772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178772).length < 2 ^ (prefixWord ++ tailWord_5178772).sum := by decide
  have hdescent : baseEnd_5178772 < baseStart_5178772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178776 : List Nat := [2, 1, 2, 5, 2, 2, 1, 1, 3, 4]
def baseStart_5178776 : Nat := 118140960795 + 5178776 * 2 ^ 59
def prefixEnd_5178776 : Nat := 4983230072969 + 3 ^ 40 * 5178776 * 2
def baseEnd_5178776 : Nat := 886400429989578416261083

theorem tailTrace_5178776 : CollatzResearch.WordTrace tailWord_5178776 prefixEnd_5178776 886400429989578416261083 := by
  unfold tailWord_5178776
  simp only [CollatzResearch.WordTrace]
  refine ⟨94442739143093245685046091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125923652190790994246728121 94442739143093245685046091)
  ·
    refine ⟨141664108714639868527569137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94442739143093245685046091 141664108714639868527569137)
    ·
      refine ⟨106248081535979901395676853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141664108714639868527569137 106248081535979901395676853)
      ·
        refine ⟨9960757643998115755844705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106248081535979901395676853 9960757643998115755844705)
        ·
          refine ⟨7470568232998586816883529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9960757643998115755844705 7470568232998586816883529)
          ·
            refine ⟨5602926174748940112662647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7470568232998586816883529 5602926174748940112662647)
            ·
              refine ⟨8404389262123410168993971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5602926174748940112662647 8404389262123410168993971)
              ·
                refine ⟨12606583893185115253490957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8404389262123410168993971 12606583893185115253490957)
                ·
                  refine ⟨4727468959944418220059109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12606583893185115253490957 4727468959944418220059109)
                  ·
                    refine ⟨886400429989578416261083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4727468959944418220059109 886400429989578416261083)
                    ·
                      rfl

theorem cell23_5178776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_5178776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178776 prefixEnd_5178776 := by exact prefixLift 5178776
  have htrace : WordTrace (prefixWord ++ tailWord_5178776) baseStart_5178776 baseEnd_5178776 := by
    simpa [prefixWord, tailWord_5178776, baseEnd_5178776] using wordTrace_append hprefix tailTrace_5178776
  have hstable : (prefixWord ++ tailWord_5178776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178776).length < 2 ^ (prefixWord ++ tailWord_5178776).sum := by decide
  have hdescent : baseEnd_5178776 < baseStart_5178776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5178802 : List Nat := [3, 2, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_5178802 : Nat := 118140960795 + 5178802 * 2 ^ 59
def prefixEnd_5178802 : Nat := 4983230072969 + 3 ^ 40 * 5178802 * 2
def baseEnd_5178802 : Nat := 886404880155250715686043

theorem tailTrace_5178802 : CollatzResearch.WordTrace tailWord_5178802 prefixEnd_5178802 886404880155250715686043 := by
  unfold tailWord_5178802
  simp only [CollatzResearch.WordTrace]
  refine ⟨47221606646023074452634665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125924284389394865207025773 47221606646023074452634665)
  ·
    refine ⟨35416204984517305839475999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47221606646023074452634665 35416204984517305839475999)
    ·
      refine ⟨53124307476775958759213999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35416204984517305839475999 53124307476775958759213999)
      ·
        refine ⟨79686461215163938138820999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53124307476775958759213999 79686461215163938138820999)
        ·
          refine ⟨119529691822745907208231499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79686461215163938138820999 119529691822745907208231499)
          ·
            refine ⟨179294537734118860812347249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119529691822745907208231499 179294537734118860812347249)
            ·
              refine ⟨134470903300589145609260437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179294537734118860812347249 134470903300589145609260437)
              ·
                refine ⟨6303323592215116200434083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134470903300589145609260437 6303323592215116200434083)
                ·
                  refine ⟨9454985388322674300651125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6303323592215116200434083 9454985388322674300651125)
                  ·
                    refine ⟨886404880155250715686043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9454985388322674300651125 886404880155250715686043)
                    ·
                      rfl

theorem cell23_5178802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_5178802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5178802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5178802 prefixEnd_5178802 := by exact prefixLift 5178802
  have htrace : WordTrace (prefixWord ++ tailWord_5178802) baseStart_5178802 baseEnd_5178802 := by
    simpa [prefixWord, tailWord_5178802, baseEnd_5178802] using wordTrace_append hprefix tailTrace_5178802
  have hstable : (prefixWord ++ tailWord_5178802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5178802).length < 2 ^ (prefixWord ++ tailWord_5178802).sum := by decide
  have hdescent : baseEnd_5178802 < baseStart_5178802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5178802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
