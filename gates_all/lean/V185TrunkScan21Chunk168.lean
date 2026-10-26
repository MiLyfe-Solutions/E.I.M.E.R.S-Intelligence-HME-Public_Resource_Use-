import V185TrunkScan21Chunk167

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_2047420 : List Nat := [2, 2, 2, 4, 2, 1, 1, 7]
def baseStart_2047420 : Nat := 118140960795 + 2047420 * 2 ^ 59
def prefixEnd_2047420 : Nat := 4983230072969 + 3 ^ 40 * 2047420 * 2
def baseEnd_2047420 : Nat := 155749712833849584227273

theorem tailTrace_2047420 : CollatzResearch.WordTrace tailWord_2047420 prefixEnd_2047420 155749712833849584227273 := by
  unfold tailWord_2047420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37337771121277243171169857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49783694828369657561559809 37337771121277243171169857)
  ·
    refine ⟨28003328340957932378377393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37337771121277243171169857 28003328340957932378377393)
    ·
      refine ⟨21002496255718449283783045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28003328340957932378377393 21002496255718449283783045)
      ·
        refine ⟨3937968047947209240709321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21002496255718449283783045 3937968047947209240709321)
        ·
          refine ⟨2953476035960406930531991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3937968047947209240709321 2953476035960406930531991)
          ·
            refine ⟨4430214053940610395797987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953476035960406930531991 4430214053940610395797987)
            ·
              refine ⟨6645321080910915593696981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430214053940610395797987 6645321080910915593696981)
              ·
                refine ⟨155749712833849584227273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6645321080910915593696981 155749712833849584227273)
                ·
                  rfl

theorem cell21_2047420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_2047420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047420 prefixEnd_2047420 := by exact prefixLift 2047420
  have htrace : WordTrace (prefixWord ++ tailWord_2047420) baseStart_2047420 baseEnd_2047420 := by
    simpa [prefixWord, tailWord_2047420, baseEnd_2047420] using wordTrace_append hprefix tailTrace_2047420
  have hstable : (prefixWord ++ tailWord_2047420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047420).length < 2 ^ (prefixWord ++ tailWord_2047420).sum := by decide
  have hdescent : baseEnd_2047420 < baseStart_2047420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047448 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_2047448 : Nat := 118140960795 + 2047448 * 2 ^ 59
def prefixEnd_2047448 : Nat := 4983230072969 + 3 ^ 40 * 2047448 * 2
def baseEnd_2047448 : Nat := 467255528483026926215095

theorem tailTrace_2047448 : CollatzResearch.WordTrace tailWord_2047448 prefixEnd_2047448 467255528483026926215095 := by
  unfold tailWord_2047448
  simp only [CollatzResearch.WordTrace]
  refine ⟨37338281743226523562179499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49784375657635364749572665 37338281743226523562179499)
  ·
    refine ⟨56007422614839785343269249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37338281743226523562179499 56007422614839785343269249)
    ·
      refine ⟨42005566961129839007451937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56007422614839785343269249 42005566961129839007451937)
      ·
        refine ⟨31504175220847379255588953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42005566961129839007451937 31504175220847379255588953)
        ·
          refine ⟨23628131415635534441691715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31504175220847379255588953 23628131415635534441691715)
          ·
            refine ⟨35442197123453301662537573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23628131415635534441691715 35442197123453301662537573)
            ·
              refine ⟨6645411960647494061725795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35442197123453301662537573 6645411960647494061725795)
              ·
                refine ⟨9968117940971241092588693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645411960647494061725795 9968117940971241092588693)
                ·
                  refine ⟨467255528483026926215095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9968117940971241092588693 467255528483026926215095)
                  ·
                    rfl

theorem cell21_2047448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_2047448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047448 prefixEnd_2047448 := by exact prefixLift 2047448
  have htrace : WordTrace (prefixWord ++ tailWord_2047448) baseStart_2047448 baseEnd_2047448 := by
    simpa [prefixWord, tailWord_2047448, baseEnd_2047448] using wordTrace_append hprefix tailTrace_2047448
  have hstable : (prefixWord ++ tailWord_2047448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047448).length < 2 ^ (prefixWord ++ tailWord_2047448).sum := by decide
  have hdescent : baseEnd_2047448 < baseStart_2047448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047502 : List Nat := [4, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_2047502 : Nat := 118140960795 + 2047502 * 2 ^ 59
def prefixEnd_2047502 : Nat := 4983230072969 + 3 ^ 40 * 2047502 * 2
def baseEnd_2047502 : Nat := 467267852018734832314985

theorem tailTrace_2047502 : CollatzResearch.WordTrace tailWord_2047502 prefixEnd_2047502 467267852018734832314985 := by
  unfold tailWord_2047502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334816628532176793353095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49785688685504942897883173 9334816628532176793353095)
  ·
    refine ⟨14002224942798265190029643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9334816628532176793353095 14002224942798265190029643)
    ·
      refine ⟨21003337414197397785044465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14002224942798265190029643 21003337414197397785044465)
      ·
        refine ⟨15752503060648048338783349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21003337414197397785044465 15752503060648048338783349)
        ·
          refine ⟨1476797161935754531760939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15752503060648048338783349 1476797161935754531760939)
          ·
            refine ⟨2215195742903631797641409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476797161935754531760939 2215195742903631797641409)
            ·
              refine ⟨1661396807177723848231057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2215195742903631797641409 1661396807177723848231057)
              ·
                refine ⟨1246047605383292886173293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1661396807177723848231057 1246047605383292886173293)
                ·
                  refine ⟨467267852018734832314985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246047605383292886173293 467267852018734832314985)
                  ·
                    rfl

theorem cell21_2047502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_2047502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047502 prefixEnd_2047502 := by exact prefixLift 2047502
  have htrace : WordTrace (prefixWord ++ tailWord_2047502) baseStart_2047502 baseEnd_2047502 := by
    simpa [prefixWord, tailWord_2047502, baseEnd_2047502] using wordTrace_append hprefix tailTrace_2047502
  have hstable : (prefixWord ++ tailWord_2047502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047502).length < 2 ^ (prefixWord ++ tailWord_2047502).sum := by decide
  have hdescent : baseEnd_2047502 < baseStart_2047502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047600 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_2047600 : Nat := 118140960795 + 2047600 * 2 ^ 59
def prefixEnd_2047600 : Nat := 4983230072969 + 3 ^ 40 * 2047600 * 2
def baseEnd_2047600 : Nat := 467290216953908439681451

theorem tailTrace_2047600 : CollatzResearch.WordTrace tailWord_2047600 prefixEnd_2047600 467290216953908439681451 := by
  unfold tailWord_2047600
  simp only [CollatzResearch.WordTrace]
  refine ⟨37341053690951188541946127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49788071587934918055928169 37341053690951188541946127)
  ·
    refine ⟨56011580536426782812919191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37341053690951188541946127 56011580536426782812919191)
    ·
      refine ⟨84017370804640174219378787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56011580536426782812919191 84017370804640174219378787)
      ·
        refine ⟨126026056206960261329068181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84017370804640174219378787 126026056206960261329068181)
        ·
          refine ⟨5907471384701262249800071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126026056206960261329068181 5907471384701262249800071)
          ·
            refine ⟨8861207077051893374700107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5907471384701262249800071 8861207077051893374700107)
            ·
              refine ⟨13291810615577840062050161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861207077051893374700107 13291810615577840062050161)
              ·
                refine ⟨9968857961683380046537621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13291810615577840062050161 9968857961683380046537621)
                ·
                  refine ⟨467290216953908439681451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9968857961683380046537621 467290216953908439681451)
                  ·
                    rfl

theorem cell21_2047600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_2047600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047600 prefixEnd_2047600 := by exact prefixLift 2047600
  have htrace : WordTrace (prefixWord ++ tailWord_2047600) baseStart_2047600 baseEnd_2047600 := by
    simpa [prefixWord, tailWord_2047600, baseEnd_2047600] using wordTrace_append hprefix tailTrace_2047600
  have hstable : (prefixWord ++ tailWord_2047600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047600).length < 2 ^ (prefixWord ++ tailWord_2047600).sum := by decide
  have hdescent : baseEnd_2047600 < baseStart_2047600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047620 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 5]
def baseStart_2047620 : Nat := 118140960795 + 2047620 * 2 ^ 59
def prefixEnd_2047620 : Nat := 4983230072969 + 3 ^ 40 * 2047620 * 2
def baseEnd_2047620 : Nat := 467294781226392849348077

theorem tailTrace_2047620 : CollatzResearch.WordTrace tailWord_2047620 prefixEnd_2047620 467294781226392849348077 := by
  unfold tailWord_2047620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37341418420914960249810157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49788557894553280333080209 37341418420914960249810157)
  ·
    refine ⟨14003031907843110093678809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37341418420914960249810157 14003031907843110093678809)
    ·
      refine ⟨10502273930882332570259107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14003031907843110093678809 10502273930882332570259107)
      ·
        refine ⟨15753410896323498855388661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10502273930882332570259107 15753410896323498855388661)
        ·
          refine ⟨1476882271530328017692687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15753410896323498855388661 1476882271530328017692687)
          ·
            refine ⟨2215323407295492026539031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1476882271530328017692687 2215323407295492026539031)
            ·
              refine ⟨3322985110943238039808547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2215323407295492026539031 3322985110943238039808547)
              ·
                refine ⟨4984477666414857059712821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3322985110943238039808547 4984477666414857059712821)
                ·
                  refine ⟨467294781226392849348077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4984477666414857059712821 467294781226392849348077)
                  ·
                    rfl

theorem cell21_2047620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_2047620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047620 prefixEnd_2047620 := by exact prefixLift 2047620
  have htrace : WordTrace (prefixWord ++ tailWord_2047620) baseStart_2047620 baseEnd_2047620 := by
    simpa [prefixWord, tailWord_2047620, baseEnd_2047620] using wordTrace_append hprefix tailTrace_2047620
  have hstable : (prefixWord ++ tailWord_2047620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047620).length < 2 ^ (prefixWord ++ tailWord_2047620).sum := by decide
  have hdescent : baseEnd_2047620 < baseStart_2047620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047634 : List Nat := [3, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_2047634 : Nat := 118140960795 + 2047634 * 2 ^ 59
def prefixEnd_2047634 : Nat := 4983230072969 + 3 ^ 40 * 2047634 * 2
def baseEnd_2047634 : Nat := 467297976217131936114715

theorem tailTrace_2047634 : CollatzResearch.WordTrace tailWord_2047634 prefixEnd_2047634 467297976217131936114715 := by
  unfold tailWord_2047634
  simp only [CollatzResearch.WordTrace]
  refine ⟨18670836865944800222657489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49788898309186133927086637 18670836865944800222657489)
  ·
    refine ⟨14003127649458600166993117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18670836865944800222657489 14003127649458600166993117)
    ·
      refine ⟨5251172868546975062622419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14003127649458600166993117 5251172868546975062622419)
      ·
        refine ⟨7876759302820462593933629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251172868546975062622419 7876759302820462593933629)
        ·
          refine ⟨2953784738557673472725111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7876759302820462593933629 2953784738557673472725111)
          ·
            refine ⟨4430677107836510209087667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2953784738557673472725111 4430677107836510209087667)
            ·
              refine ⟨6646015661754765313631501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4430677107836510209087667 6646015661754765313631501)
              ·
                refine ⟨2492255873158036992611813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6646015661754765313631501 2492255873158036992611813)
                ·
                  refine ⟨467297976217131936114715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2492255873158036992611813 467297976217131936114715)
                  ·
                    rfl

theorem cell21_2047634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_2047634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047634 prefixEnd_2047634 := by exact prefixLift 2047634
  have htrace : WordTrace (prefixWord ++ tailWord_2047634) baseStart_2047634 baseEnd_2047634 := by
    simpa [prefixWord, tailWord_2047634, baseEnd_2047634] using wordTrace_append hprefix tailTrace_2047634
  have hstable : (prefixWord ++ tailWord_2047634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047634).length < 2 ^ (prefixWord ++ tailWord_2047634).sum := by decide
  have hdescent : baseEnd_2047634 < baseStart_2047634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2047645 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 7]
def baseStart_2047645 : Nat := 118140960795 + 2047645 * 2 ^ 59
def prefixEnd_2047645 : Nat := 4983230072969 + 3 ^ 40 * 2047645 * 2
def baseEnd_2047645 : Nat := 467300486566998361431359

theorem tailTrace_2047645 : CollatzResearch.WordTrace tailWord_2047645 prefixEnd_2047645 467300486566998361431359 := by
  unfold tailWord_2047645
  simp only [CollatzResearch.WordTrace]
  refine ⟨74683748666739349769280389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49789165777826233179520259 74683748666739349769280389)
  ·
    refine ⟨14003202875013628081740073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74683748666739349769280389 14003202875013628081740073)
    ·
      refine ⟨10502402156260221061305055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14003202875013628081740073 10502402156260221061305055)
      ·
        refine ⟨15753603234390331591957583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10502402156260221061305055 15753603234390331591957583)
        ·
          refine ⟨23630404851585497387936375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15753603234390331591957583 23630404851585497387936375)
          ·
            refine ⟨35445607277378246081904563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23630404851585497387936375 35445607277378246081904563)
            ·
              refine ⟨53168410916067369122856845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35445607277378246081904563 53168410916067369122856845)
              ·
                refine ⟨19938154093525263421071317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53168410916067369122856845 19938154093525263421071317)
                ·
                  refine ⟨467300486566998361431359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19938154093525263421071317 467300486566998361431359)
                  ·
                    rfl

theorem cell21_2047645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_2047645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2047645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2047645 prefixEnd_2047645 := by exact prefixLift 2047645
  have htrace : WordTrace (prefixWord ++ tailWord_2047645) baseStart_2047645 baseEnd_2047645 := by
    simpa [prefixWord, tailWord_2047645, baseEnd_2047645] using wordTrace_append hprefix tailTrace_2047645
  have hstable : (prefixWord ++ tailWord_2047645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2047645).length < 2 ^ (prefixWord ++ tailWord_2047645).sum := by decide
  have hdescent : baseEnd_2047645 < baseStart_2047645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2047645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048042 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_2048042 : Nat := 118140960795 + 2048042 * 2 ^ 59
def prefixEnd_2048042 : Nat := 4983230072969 + 3 ^ 40 * 2048042 * 2
def baseEnd_2048042 : Nat := 467391087375813893313881

theorem tailTrace_2048042 : CollatzResearch.WordTrace tailWord_2048042 prefixEnd_2048042 467391087375813893313881 := by
  unfold tailWord_2048042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18674557111575271642870595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49798818964200724380988253 18674557111575271642870595)
  ·
    refine ⟨28011835667362907464305893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18674557111575271642870595 28011835667362907464305893)
    ·
      refine ⟨5252219187630545149557355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28011835667362907464305893 5252219187630545149557355)
      ·
        refine ⟨7878328781445817724336033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5252219187630545149557355 7878328781445817724336033)
        ·
          refine ⟨5908746586084363293252025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7878328781445817724336033 5908746586084363293252025)
          ·
            refine ⟨4431559939563272469939019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5908746586084363293252025 4431559939563272469939019)
            ·
              refine ⟨6647339909344908704908529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4431559939563272469939019 6647339909344908704908529)
              ·
                refine ⟨4985504932008681528681397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6647339909344908704908529 4985504932008681528681397)
                ·
                  refine ⟨467391087375813893313881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4985504932008681528681397 467391087375813893313881)
                  ·
                    rfl

theorem cell21_2048042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_2048042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048042 prefixEnd_2048042 := by exact prefixLift 2048042
  have htrace : WordTrace (prefixWord ++ tailWord_2048042) baseStart_2048042 baseEnd_2048042 := by
    simpa [prefixWord, tailWord_2048042, baseEnd_2048042] using wordTrace_append hprefix tailTrace_2048042
  have hstable : (prefixWord ++ tailWord_2048042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048042).length < 2 ^ (prefixWord ++ tailWord_2048042).sum := by decide
  have hdescent : baseEnd_2048042 < baseStart_2048042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048101 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 5]
def baseStart_2048101 : Nat := 118140960795 + 2048101 * 2 ^ 59
def prefixEnd_2048101 : Nat := 4983230072969 + 3 ^ 40 * 2048101 * 2
def baseEnd_2048101 : Nat := 467404551979642901830427

theorem tailTrace_2048101 : CollatzResearch.WordTrace tailWord_2048101 prefixEnd_2048101 467404551979642901830427 := by
  unfold tailWord_2048101
  simp only [CollatzResearch.WordTrace]
  refine ⟨74700380353087339647880157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49800253568724893098586771 74700380353087339647880157)
  ·
    refine ⟨28012642632407752367955059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74700380353087339647880157 28012642632407752367955059)
    ·
      refine ⟨42018963948611628551932589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28012642632407752367955059 42018963948611628551932589)
      ·
        refine ⟨15757111480729360706974721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42018963948611628551932589 15757111480729360706974721)
        ·
          refine ⟨11817833610547020530231041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15757111480729360706974721 11817833610547020530231041)
          ·
            refine ⟨8863375207910265397673281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11817833610547020530231041 8863375207910265397673281)
            ·
              refine ⟨6647531405932699048254961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8863375207910265397673281 6647531405932699048254961)
              ·
                refine ⟨4985648554449524286191221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6647531405932699048254961 4985648554449524286191221)
                ·
                  refine ⟨467404551979642901830427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4985648554449524286191221 467404551979642901830427)
                  ·
                    rfl

theorem cell21_2048101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_2048101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048101 prefixEnd_2048101 := by exact prefixLift 2048101
  have htrace : WordTrace (prefixWord ++ tailWord_2048101) baseStart_2048101 baseEnd_2048101 := by
    simpa [prefixWord, tailWord_2048101, baseEnd_2048101] using wordTrace_append hprefix tailTrace_2048101
  have hstable : (prefixWord ++ tailWord_2048101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048101).length < 2 ^ (prefixWord ++ tailWord_2048101).sum := by decide
  have hdescent : baseEnd_2048101 < baseStart_2048101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048132 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_2048132 : Nat := 118140960795 + 2048132 * 2 ^ 59
def prefixEnd_2048132 : Nat := 4983230072969 + 3 ^ 40 * 2048132 * 2
def baseEnd_2048132 : Nat := 467411626601993736813697

theorem tailTrace_2048132 : CollatzResearch.WordTrace tailWord_2048132 prefixEnd_2048132 467411626601993736813697 := by
  unfold tailWord_2048132
  simp only [CollatzResearch.WordTrace]
  refine ⟨37350755507987515971129325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49801007343983354628172433 37350755507987515971129325)
  ·
    refine ⟨14006533315495318489173497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37350755507987515971129325 14006533315495318489173497)
    ·
      refine ⟨10504899986621488866880123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14006533315495318489173497 10504899986621488866880123)
      ·
        refine ⟨15757349979932233300320185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10504899986621488866880123 15757349979932233300320185)
        ·
          refine ⟨11818012484949174975240139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15757349979932233300320185 11818012484949174975240139)
          ·
            refine ⟨17727018727423762462860209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11818012484949174975240139 17727018727423762462860209)
            ·
              refine ⟨13295264045567821847145157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17727018727423762462860209 13295264045567821847145157)
              ·
                refine ⟨2492862008543966596339717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13295264045567821847145157 2492862008543966596339717)
                ·
                  refine ⟨467411626601993736813697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2492862008543966596339717 467411626601993736813697)
                  ·
                    rfl

theorem cell21_2048132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_2048132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048132 prefixEnd_2048132 := by exact prefixLift 2048132
  have htrace : WordTrace (prefixWord ++ tailWord_2048132) baseStart_2048132 baseEnd_2048132 := by
    simpa [prefixWord, tailWord_2048132, baseEnd_2048132] using wordTrace_append hprefix tailTrace_2048132
  have hstable : (prefixWord ++ tailWord_2048132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048132).length < 2 ^ (prefixWord ++ tailWord_2048132).sum := by decide
  have hdescent : baseEnd_2048132 < baseStart_2048132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048180 : List Nat := [2, 5, 3, 1, 10]
def baseStart_2048180 : Nat := 118140960795 + 2048180 * 2 ^ 59
def prefixEnd_2048180 : Nat := 4983230072969 + 3 ^ 40 * 2048180 * 2
def baseEnd_2048180 : Nat := 5770649146369831111279

theorem tailTrace_2048180 : CollatzResearch.WordTrace tailWord_2048180 prefixEnd_2048180 5770649146369831111279 := by
  unfold tailWord_2048180
  simp only [CollatzResearch.WordTrace]
  refine ⟨37351630859900568070002997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49802174479867424093337329 37351630859900568070002997)
  ·
    refine ⟨3501715393115678256562781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37351630859900568070002997 3501715393115678256562781)
    ·
      refine ⟨1313143272418379346211043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3501715393115678256562781 1313143272418379346211043)
      ·
        refine ⟨1969714908627569019316565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313143272418379346211043 1969714908627569019316565)
        ·
          refine ⟨5770649146369831111279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1969714908627569019316565 5770649146369831111279)
          ·
            rfl

theorem cell21_2048180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 10].length) (baseStart_2048180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048180 prefixEnd_2048180 := by exact prefixLift 2048180
  have htrace : WordTrace (prefixWord ++ tailWord_2048180) baseStart_2048180 baseEnd_2048180 := by
    simpa [prefixWord, tailWord_2048180, baseEnd_2048180] using wordTrace_append hprefix tailTrace_2048180
  have hstable : (prefixWord ++ tailWord_2048180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048180).length < 2 ^ (prefixWord ++ tailWord_2048180).sum := by decide
  have hdescent : baseEnd_2048180 < baseStart_2048180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048236 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_2048236 : Nat := 118140960795 + 2048236 * 2 ^ 59
def prefixEnd_2048236 : Nat := 4983230072969 + 3 ^ 40 * 2048236 * 2
def baseEnd_2048236 : Nat := 467435360818912667080151

theorem tailTrace_2048236 : CollatzResearch.WordTrace tailWord_2048236 prefixEnd_2048236 467435360818912667080151 := by
  unfold tailWord_2048236
  simp only [CollatzResearch.WordTrace]
  refine ⟨37352652103799128852022281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49803536138398838469363041 37352652103799128852022281)
  ·
    refine ⟨28014489077849346639016711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37352652103799128852022281 28014489077849346639016711)
    ·
      refine ⟨42021733616774019958525067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28014489077849346639016711 42021733616774019958525067)
      ·
        refine ⟨63032600425161029937787601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42021733616774019958525067 63032600425161029937787601)
        ·
          refine ⟨47274450318870772453340701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63032600425161029937787601 47274450318870772453340701)
          ·
            refine ⟨17727918869576539670002763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47274450318870772453340701 17727918869576539670002763)
            ·
              refine ⟨26591878304364809505004145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17727918869576539670002763 26591878304364809505004145)
              ·
                refine ⟨19943908728273607128753109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26591878304364809505004145 19943908728273607128753109)
                ·
                  refine ⟨467435360818912667080151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19943908728273607128753109 467435360818912667080151)
                  ·
                    rfl

theorem cell21_2048236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_2048236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048236 prefixEnd_2048236 := by exact prefixLift 2048236
  have htrace : WordTrace (prefixWord ++ tailWord_2048236) baseStart_2048236 baseEnd_2048236 := by
    simpa [prefixWord, tailWord_2048236, baseEnd_2048236] using wordTrace_append hprefix tailTrace_2048236
  have hstable : (prefixWord ++ tailWord_2048236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048236).length < 2 ^ (prefixWord ++ tailWord_2048236).sum := by decide
  have hdescent : baseEnd_2048236 < baseStart_2048236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048287 : List Nat := [1, 1, 2, 4, 3, 3, 1, 3, 3]
def baseStart_2048287 : Nat := 118140960795 + 2048287 * 2 ^ 59
def prefixEnd_2048287 : Nat := 4983230072969 + 3 ^ 40 * 2048287 * 2
def baseEnd_2048287 : Nat := 467446999713747911730047

theorem tailTrace_2048287 : CollatzResearch.WordTrace tailWord_2048287 prefixEnd_2048287 467446999713747911730047 := by
  unfold tailWord_2048287
  simp only [CollatzResearch.WordTrace]
  refine ⟨74707164330413493414151115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49804776220275662276100743 74707164330413493414151115)
  ·
    refine ⟨112060746495620240121226673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74707164330413493414151115 112060746495620240121226673)
    ·
      refine ⟨84045559871715180090920005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112060746495620240121226673 84045559871715180090920005)
      ·
        refine ⟨15758542475946596267047501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84045559871715180090920005 15758542475946596267047501)
        ·
          refine ⟨5909453428479973600142813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15758542475946596267047501 5909453428479973600142813)
          ·
            refine ⟨2216045035679990100053555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5909453428479973600142813 2216045035679990100053555)
            ·
              refine ⟨3324067553519985150080333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216045035679990100053555 3324067553519985150080333)
              ·
                refine ⟨1246525332569994431280125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3324067553519985150080333 1246525332569994431280125)
                ·
                  refine ⟨467446999713747911730047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246525332569994431280125 467446999713747911730047)
                  ·
                    rfl

theorem cell21_2048287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 3].length) (baseStart_2048287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048287 prefixEnd_2048287 := by exact prefixLift 2048287
  have htrace : WordTrace (prefixWord ++ tailWord_2048287) baseStart_2048287 baseEnd_2048287 := by
    simpa [prefixWord, tailWord_2048287, baseEnd_2048287] using wordTrace_append hprefix tailTrace_2048287
  have hstable : (prefixWord ++ tailWord_2048287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048287).length < 2 ^ (prefixWord ++ tailWord_2048287).sum := by decide
  have hdescent : baseEnd_2048287 < baseStart_2048287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048318 : List Nat := [4, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_2048318 : Nat := 118140960795 + 2048318 * 2 ^ 59
def prefixEnd_2048318 : Nat := 4983230072969 + 3 ^ 40 * 2048318 * 2
def baseEnd_2048318 : Nat := 467454074336098746713317

theorem tailTrace_2048318 : CollatzResearch.WordTrace tailWord_2048318 prefixEnd_2048318 467454074336098746713317 := by
  unfold tailWord_2048318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9338536874162648213566201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49805529995534123805686405 9338536874162648213566201)
  ·
    refine ⟨7003902655621986160174651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9338536874162648213566201 7003902655621986160174651)
    ·
      refine ⟨10505853983432979240261977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7003902655621986160174651 10505853983432979240261977)
      ·
        refine ⟨7879390487574734430196483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10505853983432979240261977 7879390487574734430196483)
        ·
          refine ⟨11819085731362101645294725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7879390487574734430196483 11819085731362101645294725)
          ·
            refine ⟨2216078574630394058492761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11819085731362101645294725 2216078574630394058492761)
            ·
              refine ⟨1662058930972795543869571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2216078574630394058492761 1662058930972795543869571)
              ·
                refine ⟨2493088396459193315804357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1662058930972795543869571 2493088396459193315804357)
                ·
                  refine ⟨467454074336098746713317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493088396459193315804357 467454074336098746713317)
                  ·
                    rfl

theorem cell21_2048318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_2048318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048318 prefixEnd_2048318 := by exact prefixLift 2048318
  have htrace : WordTrace (prefixWord ++ tailWord_2048318) baseStart_2048318 baseEnd_2048318 := by
    simpa [prefixWord, tailWord_2048318, baseEnd_2048318] using wordTrace_append hprefix tailTrace_2048318
  have hstable : (prefixWord ++ tailWord_2048318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048318).length < 2 ^ (prefixWord ++ tailWord_2048318).sum := by decide
  have hdescent : baseEnd_2048318 < baseStart_2048318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048357 : List Nat := [1, 3, 1, 3, 1, 12]
def baseStart_2048357 : Nat := 118140960795 + 2048357 * 2 ^ 59
def prefixEnd_2048357 : Nat := 4983230072969 + 3 ^ 40 * 2048357 * 2
def baseEnd_2048357 : Nat := 17313443506201605391231

theorem tailTrace_2048357 : CollatzResearch.WordTrace tailWord_2048357 prefixEnd_2048357 17313443506201605391231 := by
  unfold tailWord_2048357
  simp only [CollatzResearch.WordTrace]
  refine ⟨74709717440159895369199325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49806478293439930246132883 74709717440159895369199325)
  ·
    refine ⟨28016144040059960763449747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74709717440159895369199325 28016144040059960763449747)
    ·
      refine ⟨42024216060089941145174621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28016144040059960763449747 42024216060089941145174621)
      ·
        refine ⟨15759081022533727929440483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42024216060089941145174621 15759081022533727929440483)
        ·
          refine ⟨23638621533800591894160725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15759081022533727929440483 23638621533800591894160725)
          ·
            refine ⟨17313443506201605391231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23638621533800591894160725 17313443506201605391231)
            ·
              rfl

theorem cell21_2048357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 12].length) (baseStart_2048357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048357 prefixEnd_2048357 := by exact prefixLift 2048357
  have htrace : WordTrace (prefixWord ++ tailWord_2048357) baseStart_2048357 baseEnd_2048357 := by
    simpa [prefixWord, tailWord_2048357, baseEnd_2048357] using wordTrace_append hprefix tailTrace_2048357
  have hstable : (prefixWord ++ tailWord_2048357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048357).length < 2 ^ (prefixWord ++ tailWord_2048357).sum := by decide
  have hdescent : baseEnd_2048357 < baseStart_2048357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048360 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_2048360 : Nat := 118140960795 + 2048360 * 2 ^ 59
def prefixEnd_2048360 : Nat := 4983230072969 + 3 ^ 40 * 2048360 * 2
def baseEnd_2048360 : Nat := 467463659308316007013231

theorem tailTrace_2048360 : CollatzResearch.WordTrace tailWord_2048360 prefixEnd_2048360 467463659308316007013231 := by
  unfold tailWord_2048360
  simp only [CollatzResearch.WordTrace]
  refine ⟨37354913429574513440779267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49806551239432684587705689 37354913429574513440779267)
  ·
    refine ⟨56032370144361770161168901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37354913429574513440779267 56032370144361770161168901)
    ·
      refine ⟨10506069402067831905219169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56032370144361770161168901 10506069402067831905219169)
      ·
        refine ⟨7879552051550873928914377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10506069402067831905219169 7879552051550873928914377)
        ·
          refine ⟨5909664038663155446685783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7879552051550873928914377 5909664038663155446685783)
          ·
            refine ⟨8864496057994733170028675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5909664038663155446685783 8864496057994733170028675)
            ·
              refine ⟨13296744086992099755043013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8864496057994733170028675 13296744086992099755043013)
              ·
                refine ⟨2493139516311018704070565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13296744086992099755043013 2493139516311018704070565)
                ·
                  refine ⟨467463659308316007013231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493139516311018704070565 467463659308316007013231)
                  ·
                    rfl

theorem cell21_2048360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_2048360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048360 prefixEnd_2048360 := by exact prefixLift 2048360
  have htrace : WordTrace (prefixWord ++ tailWord_2048360) baseStart_2048360 baseEnd_2048360 := by
    simpa [prefixWord, tailWord_2048360, baseEnd_2048360] using wordTrace_append hprefix tailTrace_2048360
  have hstable : (prefixWord ++ tailWord_2048360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048360).length < 2 ^ (prefixWord ++ tailWord_2048360).sum := by decide
  have hdescent : baseEnd_2048360 < baseStart_2048360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048419 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 6]
def baseStart_2048419 : Nat := 118140960795 + 2048419 * 2 ^ 59
def prefixEnd_2048419 : Nat := 4983230072969 + 3 ^ 40 * 2048419 * 2
def baseEnd_2048419 : Nat := 467477123912145015529777

theorem tailTrace_2048419 : CollatzResearch.WordTrace tailWord_2048419 prefixEnd_2048419 467477123912145015529777 := by
  unfold tailWord_2048419
  simp only [CollatzResearch.WordTrace]
  refine ⟨74711978765935279957956311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49807985843956853305304207 74711978765935279957956311)
  ·
    refine ⟨112067968148902919936934467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74711978765935279957956311 112067968148902919936934467)
    ·
      refine ⟨168101952223354379905401701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112067968148902919936934467 168101952223354379905401701)
      ·
        refine ⟨31519116041878946232262819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168101952223354379905401701 31519116041878946232262819)
        ·
          refine ⟨47278674062818419348394229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31519116041878946232262819 47278674062818419348394229)
          ·
            refine ⟨4432375693389226813911959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47278674062818419348394229 4432375693389226813911959)
            ·
              refine ⟨6648563540083840220867939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4432375693389226813911959 6648563540083840220867939)
              ·
                refine ⟨9972845310125760331301909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6648563540083840220867939 9972845310125760331301909)
                ·
                  refine ⟨467477123912145015529777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9972845310125760331301909 467477123912145015529777)
                  ·
                    rfl

theorem cell21_2048419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_2048419 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048419 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048419 prefixEnd_2048419 := by exact prefixLift 2048419
  have htrace : WordTrace (prefixWord ++ tailWord_2048419) baseStart_2048419 baseEnd_2048419 := by
    simpa [prefixWord, tailWord_2048419, baseEnd_2048419] using wordTrace_append hprefix tailTrace_2048419
  have hstable : (prefixWord ++ tailWord_2048419).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048419).length < 2 ^ (prefixWord ++ tailWord_2048419).sum := by decide
  have hdescent : baseEnd_2048419 < baseStart_2048419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048509 : List Nat := [1, 4, 1, 1, 1, 3, 1, 9]
def baseStart_2048509 : Nat := 118140960795 + 2048509 * 2 ^ 59
def prefixEnd_2048509 : Nat := 4983230072969 + 3 ^ 40 * 2048509 * 2
def baseEnd_2048509 : Nat := 155832554379441619676531

theorem tailTrace_2048509 : CollatzResearch.WordTrace tailWord_2048509 prefixEnd_2048509 155832554379441619676531 := by
  unfold tailWord_2048509
  simp only [CollatzResearch.WordTrace]
  refine ⟨74715261335609225328732581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49810174223739483552488387 74715261335609225328732581)
  ·
    refine ⟨14009111500426729749137359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74715261335609225328732581 14009111500426729749137359)
    ·
      refine ⟨21013667250640094623706039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14009111500426729749137359 21013667250640094623706039)
      ·
        refine ⟨31520500875960141935559059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21013667250640094623706039 31520500875960141935559059)
        ·
          refine ⟨47280751313940212903338589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31520500875960141935559059 47280751313940212903338589)
          ·
            refine ⟨17730281742727579838751971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47280751313940212903338589 17730281742727579838751971)
            ·
              refine ⟨26595422614091369758127957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17730281742727579838751971 26595422614091369758127957)
              ·
                refine ⟨155832554379441619676531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26595422614091369758127957 155832554379441619676531)
                ·
                  rfl

theorem cell21_2048509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 9].length) (baseStart_2048509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048509 prefixEnd_2048509 := by exact prefixLift 2048509
  have htrace : WordTrace (prefixWord ++ tailWord_2048509) baseStart_2048509 baseEnd_2048509 := by
    simpa [prefixWord, tailWord_2048509, baseEnd_2048509] using wordTrace_append hprefix tailTrace_2048509
  have hstable : (prefixWord ++ tailWord_2048509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048509).length < 2 ^ (prefixWord ++ tailWord_2048509).sum := by decide
  have hdescent : baseEnd_2048509 < baseStart_2048509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048532 : List Nat := [2, 4, 3, 1, 1, 1, 4, 2, 3]
def baseStart_2048532 : Nat := 118140960795 + 2048532 * 2 ^ 59
def prefixEnd_2048532 : Nat := 4983230072969 + 3 ^ 40 * 2048532 * 2
def baseEnd_2048532 : Nat := 467502912051681930146213

theorem tailTrace_2048532 : CollatzResearch.WordTrace tailWord_2048532 prefixEnd_2048532 467502912051681930146213 := by
  unfold tailWord_2048532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37358050107262950128409925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49810733476350600171213233 37358050107262950128409925)
  ·
    refine ⟨7004634395111803149076861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37358050107262950128409925 7004634395111803149076861)
    ·
      refine ⟨2626737898166926180903823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7004634395111803149076861 2626737898166926180903823)
      ·
        refine ⟨3940106847250389271355735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2626737898166926180903823 3940106847250389271355735)
        ·
          refine ⟨5910160270875583907033603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3940106847250389271355735 5910160270875583907033603)
          ·
            refine ⟨8865240406313375860550405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5910160270875583907033603 8865240406313375860550405)
            ·
              refine ⟨1662232576183757973853201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8865240406313375860550405 1662232576183757973853201)
              ·
                refine ⟨1246674432137818480389901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662232576183757973853201 1246674432137818480389901)
                ·
                  refine ⟨467502912051681930146213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246674432137818480389901 467502912051681930146213)
                  ·
                    rfl

theorem cell21_2048532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_2048532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048532 prefixEnd_2048532 := by exact prefixLift 2048532
  have htrace : WordTrace (prefixWord ++ tailWord_2048532) baseStart_2048532 baseEnd_2048532 := by
    simpa [prefixWord, tailWord_2048532, baseEnd_2048532] using wordTrace_append hprefix tailTrace_2048532
  have hstable : (prefixWord ++ tailWord_2048532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048532).length < 2 ^ (prefixWord ++ tailWord_2048532).sum := by decide
  have hdescent : baseEnd_2048532 < baseStart_2048532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048580 : List Nat := [2, 3, 5, 1, 2, 1, 1, 2, 4]
def baseStart_2048580 : Nat := 118140960795 + 2048580 * 2 ^ 59
def prefixEnd_2048580 : Nat := 4983230072969 + 3 ^ 40 * 2048580 * 2
def baseEnd_2048580 : Nat := 467513866305644513346115

theorem tailTrace_2048580 : CollatzResearch.WordTrace tailWord_2048580 prefixEnd_2048580 467513866305644513346115 := by
  unfold tailWord_2048580
  simp only [CollatzResearch.WordTrace]
  refine ⟨37358925459176002227283597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49811900612234669636378129 37358925459176002227283597)
  ·
    refine ⟨14009597047191000835231349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37358925459176002227283597 14009597047191000835231349)
    ·
      refine ⟨1313399723174156328302939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14009597047191000835231349 1313399723174156328302939)
      ·
        refine ⟨1970099584761234492454409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313399723174156328302939 1970099584761234492454409)
        ·
          refine ⟨1477574688570925869340807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1970099584761234492454409 1477574688570925869340807)
          ·
            refine ⟨2216362032856388804011211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1477574688570925869340807 2216362032856388804011211)
            ·
              refine ⟨3324543049284583206016817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216362032856388804011211 3324543049284583206016817)
              ·
                refine ⟨2493407286963437404512613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3324543049284583206016817 2493407286963437404512613)
                ·
                  refine ⟨467513866305644513346115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493407286963437404512613 467513866305644513346115)
                  ·
                    rfl

theorem cell21_2048580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_2048580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048580 prefixEnd_2048580 := by exact prefixLift 2048580
  have htrace : WordTrace (prefixWord ++ tailWord_2048580) baseStart_2048580 baseEnd_2048580 := by
    simpa [prefixWord, tailWord_2048580, baseEnd_2048580] using wordTrace_append hprefix tailTrace_2048580
  have hstable : (prefixWord ++ tailWord_2048580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048580).length < 2 ^ (prefixWord ++ tailWord_2048580).sum := by decide
  have hdescent : baseEnd_2048580 < baseStart_2048580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048642 : List Nat := [3, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2048642 : Nat := 118140960795 + 2048642 * 2 ^ 59
def prefixEnd_2048642 : Nat := 4983230072969 + 3 ^ 40 * 2048642 * 2
def baseEnd_2048642 : Nat := 467528015550346183312655

theorem tailTrace_2048642 : CollatzResearch.WordTrace tailWord_2048642 prefixEnd_2048642 467528015550346183312655 := by
  unfold tailWord_2048642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680028061031847260831045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49813408162751592695549453 18680028061031847260831045)
  ·
    refine ⟨3502505261443471361405821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18680028061031847260831045 3502505261443471361405821)
    ·
      refine ⟨1313439473041301760527183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3502505261443471361405821 1313439473041301760527183)
      ·
        refine ⟨1970159209561952640790775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1313439473041301760527183 1970159209561952640790775)
        ·
          refine ⟨2955238814342928961186163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970159209561952640790775 2955238814342928961186163)
          ·
            refine ⟨4432858221514393441779245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955238814342928961186163 4432858221514393441779245)
            ·
              refine ⟨1662321833067897540667217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4432858221514393441779245 1662321833067897540667217)
              ·
                refine ⟨1246741374800923155500413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662321833067897540667217 1246741374800923155500413)
                ·
                  refine ⟨467528015550346183312655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246741374800923155500413 467528015550346183312655)
                  ·
                    rfl

theorem cell21_2048642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2048642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048642 prefixEnd_2048642 := by exact prefixLift 2048642
  have htrace : WordTrace (prefixWord ++ tailWord_2048642) baseStart_2048642 baseEnd_2048642 := by
    simpa [prefixWord, tailWord_2048642, baseEnd_2048642] using wordTrace_append hprefix tailTrace_2048642
  have hstable : (prefixWord ++ tailWord_2048642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048642).length < 2 ^ (prefixWord ++ tailWord_2048642).sum := by decide
  have hdescent : baseEnd_2048642 < baseStart_2048642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048647 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 4]
def baseStart_2048647 : Nat := 118140960795 + 2048647 * 2 ^ 59
def prefixEnd_2048647 : Nat := 4983230072969 + 3 ^ 40 * 2048647 * 2
def baseEnd_2048647 : Nat := 467529156618467285729311

theorem tailTrace_2048647 : CollatzResearch.WordTrace tailWord_2048647 prefixEnd_2048647 467529156618467285729311 := by
  unfold tailWord_2048647
  simp only [CollatzResearch.WordTrace]
  refine ⟨74720294609109274897256195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49813529739406183264837463 74720294609109274897256195)
  ·
    refine ⟨112080441913663912345884293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74720294609109274897256195 112080441913663912345884293)
    ·
      refine ⟨21015082858811983564853305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112080441913663912345884293 21015082858811983564853305)
      ·
        refine ⟨15761312144108987673639979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21015082858811983564853305 15761312144108987673639979)
        ·
          refine ⟨23641968216163481510459969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15761312144108987673639979 23641968216163481510459969)
          ·
            refine ⟨17731476162122611132844977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23641968216163481510459969 17731476162122611132844977)
            ·
              refine ⟨13298607121591958349633733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17731476162122611132844977 13298607121591958349633733)
              ·
                refine ⟨2493488835298492190556325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13298607121591958349633733 2493488835298492190556325)
                ·
                  refine ⟨467529156618467285729311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493488835298492190556325 467529156618467285729311)
                  ·
                    rfl

theorem cell21_2048647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 4].length) (baseStart_2048647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048647 prefixEnd_2048647 := by exact prefixLift 2048647
  have htrace : WordTrace (prefixWord ++ tailWord_2048647) baseStart_2048647 baseEnd_2048647 := by
    simpa [prefixWord, tailWord_2048647, baseEnd_2048647] using wordTrace_append hprefix tailTrace_2048647
  have hstable : (prefixWord ++ tailWord_2048647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048647).length < 2 ^ (prefixWord ++ tailWord_2048647).sum := by decide
  have hdescent : baseEnd_2048647 < baseStart_2048647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048650 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_2048650 : Nat := 118140960795 + 2048650 * 2 ^ 59
def prefixEnd_2048650 : Nat := 4983230072969 + 3 ^ 40 * 2048650 * 2
def baseEnd_2048650 : Nat := 467529841259339947179305

theorem tailTrace_2048650 : CollatzResearch.WordTrace tailWord_2048650 prefixEnd_2048650 467529841259339947179305 := by
  unfold tailWord_2048650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18680101007024601602403851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49813602685398937606410269 18680101007024601602403851)
  ·
    refine ⟨28020151510536902403605777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18680101007024601602403851 28020151510536902403605777)
    ·
      refine ⟨21015113632902676802704333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28020151510536902403605777 21015113632902676802704333)
      ·
        refine ⟨7880667612338503801014125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21015113632902676802704333 7880667612338503801014125)
        ·
          refine ⟨2955250354626938925380297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7880667612338503801014125 2955250354626938925380297)
          ·
            refine ⟨2216437765970204194035223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2955250354626938925380297 2216437765970204194035223)
            ·
              refine ⟨3324656648955306291052835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216437765970204194035223 3324656648955306291052835)
              ·
                refine ⟨4986984973432959436579253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3324656648955306291052835 4986984973432959436579253)
                ·
                  refine ⟨467529841259339947179305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4986984973432959436579253 467529841259339947179305)
                  ·
                    rfl

theorem cell21_2048650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_2048650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048650 prefixEnd_2048650 := by exact prefixLift 2048650
  have htrace : WordTrace (prefixWord ++ tailWord_2048650) baseStart_2048650 baseEnd_2048650 := by
    simpa [prefixWord, tailWord_2048650, baseEnd_2048650] using wordTrace_append hprefix tailTrace_2048650
  have hstable : (prefixWord ++ tailWord_2048650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048650).length < 2 ^ (prefixWord ++ tailWord_2048650).sum := by decide
  have hdescent : baseEnd_2048650 < baseStart_2048650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048802 : List Nat := [3, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2048802 : Nat := 118140960795 + 2048802 * 2 ^ 59
def prefixEnd_2048802 : Nat := 4983230072969 + 3 ^ 40 * 2048802 * 2
def baseEnd_2048802 : Nat := 467564529730221460645661

theorem tailTrace_2048802 : CollatzResearch.WordTrace tailWord_2048802 prefixEnd_2048802 467564529730221460645661 := by
  unfold tailWord_2048802
  simp only [CollatzResearch.WordTrace]
  refine ⟨18681486980886934092287165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49817298615698490912765773 18681486980886934092287165)
  ·
    refine ⟨7005557617832600284607687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18681486980886934092287165 7005557617832600284607687)
    ·
      refine ⟨10508336426748900426911531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7005557617832600284607687 10508336426748900426911531)
      ·
        refine ⟨15762504640123350640367297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10508336426748900426911531 15762504640123350640367297)
        ·
          refine ⟨11821878480092512980275473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15762504640123350640367297 11821878480092512980275473)
          ·
            refine ⟨8866408860069384735206605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11821878480092512980275473 8866408860069384735206605)
            ·
              refine ⟨3324903322526019275702477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8866408860069384735206605 3324903322526019275702477)
              ·
                refine ⟨1246838745947257228388429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3324903322526019275702477 1246838745947257228388429)
                ·
                  refine ⟨467564529730221460645661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246838745947257228388429 467564529730221460645661)
                  ·
                    rfl

theorem cell21_2048802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2048802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048802 prefixEnd_2048802 := by exact prefixLift 2048802
  have htrace : WordTrace (prefixWord ++ tailWord_2048802) baseStart_2048802 baseEnd_2048802 := by
    simpa [prefixWord, tailWord_2048802, baseEnd_2048802] using wordTrace_append hprefix tailTrace_2048802
  have hstable : (prefixWord ++ tailWord_2048802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048802).length < 2 ^ (prefixWord ++ tailWord_2048802).sum := by decide
  have hdescent : baseEnd_2048802 < baseStart_2048802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048833 : List Nat := [1, 2, 5, 3, 1, 1, 1, 3, 4]
def baseStart_2048833 : Nat := 118140960795 + 2048833 * 2 ^ 59
def prefixEnd_2048833 : Nat := 4983230072969 + 3 ^ 40 * 2048833 * 2
def baseEnd_2048833 : Nat := 467571604352572295628931

theorem tailTrace_2048833 : CollatzResearch.WordTrace tailWord_2048833 prefixEnd_2048833 467571604352572295628931 := by
  unfold tailWord_2048833
  simp only [CollatzResearch.WordTrace]
  refine ⟨74727078586435428663527153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49818052390956952442351435 74727078586435428663527153)
  ·
    refine ⟨56045308939826571497645365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74727078586435428663527153 56045308939826571497645365)
    ·
      refine ⟨5254247713108741077904253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56045308939826571497645365 5254247713108741077904253)
      ·
        refine ⟨1970342892415777904214095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5254247713108741077904253 1970342892415777904214095)
        ·
          refine ⟨2955514338623666856321143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970342892415777904214095 2955514338623666856321143)
          ·
            refine ⟨4433271507935500284481715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955514338623666856321143 4433271507935500284481715)
            ·
              refine ⟨6649907261903250426722573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4433271507935500284481715 6649907261903250426722573)
              ·
                refine ⟨2493715223213718910020965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6649907261903250426722573 2493715223213718910020965)
                ·
                  refine ⟨467571604352572295628931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2493715223213718910020965 467571604352572295628931)
                  ·
                    rfl

theorem cell21_2048833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_2048833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048833 prefixEnd_2048833 := by exact prefixLift 2048833
  have htrace : WordTrace (prefixWord ++ tailWord_2048833) baseStart_2048833 baseEnd_2048833 := by
    simpa [prefixWord, tailWord_2048833, baseEnd_2048833] using wordTrace_append hprefix tailTrace_2048833
  have hstable : (prefixWord ++ tailWord_2048833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048833).length < 2 ^ (prefixWord ++ tailWord_2048833).sum := by decide
  have hdescent : baseEnd_2048833 < baseStart_2048833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048889 : List Nat := [1, 2, 1, 3, 2, 3, 3, 6]
def baseStart_2048889 : Nat := 118140960795 + 2048889 * 2 ^ 59
def prefixEnd_2048889 : Nat := 4983230072969 + 3 ^ 40 * 2048889 * 2
def baseEnd_2048889 : Nat := 155861461438509547565161

theorem tailTrace_2048889 : CollatzResearch.WordTrace tailWord_2048889 prefixEnd_2048889 155861461438509547565161 := by
  unfold tailWord_2048889
  simp only [CollatzResearch.WordTrace]
  refine ⟨74729121074232550227565721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49819414049488366818377147 74729121074232550227565721)
  ·
    refine ⟨56046840805674412670674291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74729121074232550227565721 56046840805674412670674291)
    ·
      refine ⟨84070261208511619006011437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56046840805674412670674291 84070261208511619006011437)
      ·
        refine ⟨31526347953191857127254289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84070261208511619006011437 31526347953191857127254289)
        ·
          refine ⟨23644760964893892845440717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31526347953191857127254289 23644760964893892845440717)
          ·
            refine ⟨8866785361835209817040269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23644760964893892845440717 8866785361835209817040269)
            ·
              refine ⟨3325044510688203681390101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8866785361835209817040269 3325044510688203681390101)
              ·
                refine ⟨155861461438509547565161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3325044510688203681390101 155861461438509547565161)
                ·
                  rfl

theorem cell21_2048889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 6].length) (baseStart_2048889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048889 prefixEnd_2048889 := by exact prefixLift 2048889
  have htrace : WordTrace (prefixWord ++ tailWord_2048889) baseStart_2048889 baseEnd_2048889 := by
    simpa [prefixWord, tailWord_2048889, baseEnd_2048889] using wordTrace_append hprefix tailTrace_2048889
  have hstable : (prefixWord ++ tailWord_2048889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048889).length < 2 ^ (prefixWord ++ tailWord_2048889).sum := by decide
  have hdescent : baseEnd_2048889 < baseStart_2048889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2048982 : List Nat := [5, 2, 1, 1, 2, 1, 9]
def baseStart_2048982 : Nat := 118140960795 + 2048982 * 2 ^ 59
def prefixEnd_2048982 : Nat := 4983230072969 + 3 ^ 40 * 2048982 * 2
def baseEnd_2048982 : Nat := 51956178686953460849477

theorem tailTrace_2048982 : CollatzResearch.WordTrace tailWord_2048982 prefixEnd_2048982 51956178686953460849477 := by
  unfold tailWord_2048982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4670782066430976694418825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49821675375263751407134133 4670782066430976694418825)
  ·
    refine ⟨3503086549823232520814119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4670782066430976694418825 3503086549823232520814119)
    ·
      refine ⟨5254629824734848781221179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503086549823232520814119 5254629824734848781221179)
      ·
        refine ⟨7881944737102273171831769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254629824734848781221179 7881944737102273171831769)
        ·
          refine ⟨5911458552826704878873827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7881944737102273171831769 5911458552826704878873827)
          ·
            refine ⟨8867187829240057318310741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5911458552826704878873827 8867187829240057318310741)
            ·
              refine ⟨51956178686953460849477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8867187829240057318310741 51956178686953460849477)
              ·
                rfl

theorem cell21_2048982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 9].length) (baseStart_2048982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2048982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2048982 prefixEnd_2048982 := by exact prefixLift 2048982
  have htrace : WordTrace (prefixWord ++ tailWord_2048982) baseStart_2048982 baseEnd_2048982 := by
    simpa [prefixWord, tailWord_2048982, baseEnd_2048982] using wordTrace_append hprefix tailTrace_2048982
  have hstable : (prefixWord ++ tailWord_2048982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2048982).length < 2 ^ (prefixWord ++ tailWord_2048982).sum := by decide
  have hdescent : baseEnd_2048982 < baseStart_2048982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2048982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049047 : List Nat := [1, 1, 3, 5, 1, 3, 2, 2, 3]
def baseStart_2049047 : Nat := 118140960795 + 2049047 * 2 ^ 59
def prefixEnd_2049047 : Nat := 4983230072969 + 3 ^ 40 * 2049047 * 2
def baseEnd_2049047 : Nat := 467620442068155479061827

theorem tailTrace_2049047 : CollatzResearch.WordTrace tailWord_2049047 prefixEnd_2049047 467620442068155479061827 := by
  unfold tailWord_2049047
  simp only [CollatzResearch.WordTrace]
  refine ⟨74734883807660143211817395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49823255871773428807878263 74734883807660143211817395)
  ·
    refine ⟨112102325711490214817726093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74734883807660143211817395 112102325711490214817726093)
    ·
      refine ⟨42038372141808830556647285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112102325711490214817726093 42038372141808830556647285)
      ·
        refine ⟨3941097388294577864685683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42038372141808830556647285 3941097388294577864685683)
        ·
          refine ⟨5911646082441866797028525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941097388294577864685683 5911646082441866797028525)
          ·
            refine ⟨2216867280915700048885697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5911646082441866797028525 2216867280915700048885697)
            ·
              refine ⟨1662650460686775036664273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2216867280915700048885697 1662650460686775036664273)
              ·
                refine ⟨1246987845515081277498205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662650460686775036664273 1246987845515081277498205)
                ·
                  refine ⟨467620442068155479061827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246987845515081277498205 467620442068155479061827)
                  ·
                    rfl

theorem cell21_2049047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 2, 3].length) (baseStart_2049047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049047 prefixEnd_2049047 := by exact prefixLift 2049047
  have htrace : WordTrace (prefixWord ++ tailWord_2049047) baseStart_2049047 baseEnd_2049047 := by
    simpa [prefixWord, tailWord_2049047, baseEnd_2049047] using wordTrace_append hprefix tailTrace_2049047
  have hstable : (prefixWord ++ tailWord_2049047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049047).length < 2 ^ (prefixWord ++ tailWord_2049047).sum := by decide
  have hdescent : baseEnd_2049047 < baseStart_2049047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049058 : List Nat := [3, 3, 1, 1, 1, 5, 1, 6]
def baseStart_2049058 : Nat := 118140960795 + 2049058 * 2 ^ 59
def prefixEnd_2049058 : Nat := 4983230072969 + 3 ^ 40 * 2049058 * 2
def baseEnd_2049058 : Nat := 155874317472673968126157

theorem tailTrace_2049058 : CollatzResearch.WordTrace tailWord_2049058 prefixEnd_2049058 155874317472673968126157 := by
  unfold tailWord_2049058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18683821252655073022616957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49823523340413528060311885 18683821252655073022616957)
  ·
    refine ⟨7006432969745652383481359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18683821252655073022616957 7006432969745652383481359)
    ·
      refine ⟨10509649454618478575222039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7006432969745652383481359 10509649454618478575222039)
      ·
        refine ⟨15764474181927717862833059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10509649454618478575222039 15764474181927717862833059)
        ·
          refine ⟨23646711272891576794249589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15764474181927717862833059 23646711272891576794249589)
          ·
            refine ⟨2216879181833585324460899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23646711272891576794249589 2216879181833585324460899)
            ·
              refine ⟨3325318772750377986691349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2216879181833585324460899 3325318772750377986691349)
              ·
                refine ⟨155874317472673968126157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3325318772750377986691349 155874317472673968126157)
                ·
                  rfl

theorem cell21_2049058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_2049058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049058 prefixEnd_2049058 := by exact prefixLift 2049058
  have htrace : WordTrace (prefixWord ++ tailWord_2049058) baseStart_2049058 baseEnd_2049058 := by
    simpa [prefixWord, tailWord_2049058, baseEnd_2049058] using wordTrace_append hprefix tailTrace_2049058
  have hstable : (prefixWord ++ tailWord_2049058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049058).length < 2 ^ (prefixWord ++ tailWord_2049058).sum := by decide
  have hdescent : baseEnd_2049058 < baseStart_2049058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049134 : List Nat := [4, 1, 2, 2, 1, 2, 4, 5]
def baseStart_2049134 : Nat := 118140960795 + 2049134 * 2 ^ 59
def prefixEnd_2049134 : Nat := 4983230072969 + 3 ^ 40 * 2049134 * 2
def baseEnd_2049134 : Nat := 155880098884487553703883

theorem tailTrace_2049134 : CollatzResearch.WordTrace tailWord_2049134 prefixEnd_2049134 155880098884487553703883 := by
  unfold tailWord_2049134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342257119793119633779307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49825371305563304713489637 9342257119793119633779307)
  ·
    refine ⟨14013385679689679450668961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9342257119793119633779307 14013385679689679450668961)
    ·
      refine ⟨10510039259767259588001721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14013385679689679450668961 10510039259767259588001721)
      ·
        refine ⟨7882529444825444691001291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10510039259767259588001721 7882529444825444691001291)
        ·
          refine ⟨11823794167238167036501937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7882529444825444691001291 11823794167238167036501937)
          ·
            refine ⟨8867845625428625277376453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11823794167238167036501937 8867845625428625277376453)
            ·
              refine ⟨1662721054767867239508085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8867845625428625277376453 1662721054767867239508085)
              ·
                refine ⟨155880098884487553703883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1662721054767867239508085 155880098884487553703883)
                ·
                  rfl

theorem cell21_2049134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_2049134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049134 prefixEnd_2049134 := by exact prefixLift 2049134
  have htrace : WordTrace (prefixWord ++ tailWord_2049134) baseStart_2049134 baseEnd_2049134 := by
    simpa [prefixWord, tailWord_2049134, baseEnd_2049134] using wordTrace_append hprefix tailTrace_2049134
  have hstable : (prefixWord ++ tailWord_2049134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049134).length < 2 ^ (prefixWord ++ tailWord_2049134).sum := by decide
  have hdescent : baseEnd_2049134 < baseStart_2049134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049162 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_2049162 : Nat := 118140960795 + 2049162 * 2 ^ 59
def prefixEnd_2049162 : Nat := 4983230072969 + 3 ^ 40 * 2049162 * 2
def baseEnd_2049162 : Nat := 467646686634940834644925

theorem tailTrace_2049162 : CollatzResearch.WordTrace tailWord_2049162 prefixEnd_2049162 467646686634940834644925 := by
  unfold tailWord_2049162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18684769550560879463063435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49826052134829011901502493 18684769550560879463063435)
  ·
    refine ⟨28027154325841319194595153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18684769550560879463063435 28027154325841319194595153)
    ·
      refine ⟨21020365744380989395946365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28027154325841319194595153 21020365744380989395946365)
      ·
        refine ⟨7882637154142871023479887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21020365744380989395946365 7882637154142871023479887)
        ·
          refine ⟨11823955731214306535219831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7882637154142871023479887 11823955731214306535219831)
          ·
            refine ⟨17735933596821459802829747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11823955731214306535219831 17735933596821459802829747)
            ·
              refine ⟨26603900395232189704244621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17735933596821459802829747 26603900395232189704244621)
              ·
                refine ⟨9976462648212071139091733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26603900395232189704244621 9976462648212071139091733)
                ·
                  refine ⟨467646686634940834644925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9976462648212071139091733 467646686634940834644925)
                  ·
                    rfl

theorem cell21_2049162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_2049162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049162 prefixEnd_2049162 := by exact prefixLift 2049162
  have htrace : WordTrace (prefixWord ++ tailWord_2049162) baseStart_2049162 baseEnd_2049162 := by
    simpa [prefixWord, tailWord_2049162, baseEnd_2049162] using wordTrace_append hprefix tailTrace_2049162
  have hstable : (prefixWord ++ tailWord_2049162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049162).length < 2 ^ (prefixWord ++ tailWord_2049162).sum := by decide
  have hdescent : baseEnd_2049162 < baseStart_2049162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049252 : List Nat := [2, 3, 1, 1, 1, 2, 2, 9]
def baseStart_2049252 : Nat := 118140960795 + 2049252 * 2 ^ 59
def prefixEnd_2049252 : Nat := 4983230072969 + 3 ^ 40 * 2049252 * 2
def baseEnd_2049252 : Nat := 155889075287040226048247

theorem tailTrace_2049252 : CollatzResearch.WordTrace tailWord_2049252 prefixEnd_2049252 155889075287040226048247 := by
  unfold tailWord_2049252
  simp only [CollatzResearch.WordTrace]
  refine ⟨37371180385958731611515005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49828240514611642148686673 37371180385958731611515005)
  ·
    refine ⟨14014192644734524354318127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37371180385958731611515005 14014192644734524354318127)
    ·
      refine ⟨21021288967101786531477191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14014192644734524354318127 21021288967101786531477191)
      ·
        refine ⟨31531933450652679797215787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21021288967101786531477191 31531933450652679797215787)
        ·
          refine ⟨47297900175979019695823681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31531933450652679797215787 47297900175979019695823681)
          ·
            refine ⟨35473425131984264771867761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47297900175979019695823681 35473425131984264771867761)
            ·
              refine ⟨26605068848988198578900821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35473425131984264771867761 26605068848988198578900821)
              ·
                refine ⟨155889075287040226048247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26605068848988198578900821 155889075287040226048247)
                ·
                  rfl

theorem cell21_2049252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_2049252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049252 prefixEnd_2049252 := by exact prefixLift 2049252
  have htrace : WordTrace (prefixWord ++ tailWord_2049252) baseStart_2049252 baseEnd_2049252 := by
    simpa [prefixWord, tailWord_2049252, baseEnd_2049252] using wordTrace_append hprefix tailTrace_2049252
  have hstable : (prefixWord ++ tailWord_2049252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049252).length < 2 ^ (prefixWord ++ tailWord_2049252).sum := by decide
  have hdescent : baseEnd_2049252 < baseStart_2049252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049283 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 5]
def baseStart_2049283 : Nat := 118140960795 + 2049283 * 2 ^ 59
def prefixEnd_2049283 : Nat := 4983230072969 + 3 ^ 40 * 2049283 * 2
def baseEnd_2049283 : Nat := 467674300483471513128011

theorem tailTrace_2049283 : CollatzResearch.WordTrace tailWord_2049283 prefixEnd_2049283 467674300483471513128011 := by
  unfold tailWord_2049283
  simp only [CollatzResearch.WordTrace]
  refine ⟨74743491434805155517408503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49828994289870103678272335 74743491434805155517408503)
  ·
    refine ⟨112115237152207733276112755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74743491434805155517408503 112115237152207733276112755)
    ·
      refine ⟨168172855728311599914169133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112115237152207733276112755 168172855728311599914169133)
      ·
        refine ⟨63064820898116849967813425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168172855728311599914169133 63064820898116849967813425)
        ·
          refine ⟨47298615673587637475860069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63064820898116849967813425 47298615673587637475860069)
          ·
            refine ⟨8868490438797682026723763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47298615673587637475860069 8868490438797682026723763)
            ·
              refine ⟨13302735658196523040085645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868490438797682026723763 13302735658196523040085645)
              ·
                refine ⟨4988525871823696140032117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13302735658196523040085645 4988525871823696140032117)
                ·
                  refine ⟨467674300483471513128011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4988525871823696140032117 467674300483471513128011)
                  ·
                    rfl

theorem cell21_2049283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_2049283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049283 prefixEnd_2049283 := by exact prefixLift 2049283
  have htrace : WordTrace (prefixWord ++ tailWord_2049283) baseStart_2049283 baseEnd_2049283 := by
    simpa [prefixWord, tailWord_2049283, baseEnd_2049283] using wordTrace_append hprefix tailTrace_2049283
  have hstable : (prefixWord ++ tailWord_2049283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049283).length < 2 ^ (prefixWord ++ tailWord_2049283).sum := by decide
  have hdescent : baseEnd_2049283 < baseStart_2049283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049317 : List Nat := [1, 3, 1, 2, 4, 1, 3, 3, 3]
def baseStart_2049317 : Nat := 118140960795 + 2049317 * 2 ^ 59
def prefixEnd_2049317 : Nat := 4983230072969 + 3 ^ 40 * 2049317 * 2
def baseEnd_2049317 : Nat := 467682059746695009561275

theorem tailTrace_2049317 : CollatzResearch.WordTrace tailWord_2049317 prefixEnd_2049317 467682059746695009561275 := by
  unfold tailWord_2049317
  simp only [CollatzResearch.WordTrace]
  refine ⟨74744731516681979324146205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49829821011121319549430803 74744731516681979324146205)
  ·
    refine ⟨28029274318755742246554827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74744731516681979324146205 28029274318755742246554827)
    ·
      refine ⟨42043911478133613369832241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28029274318755742246554827 42043911478133613369832241)
      ·
        refine ⟨31532933608600210027374181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42043911478133613369832241 31532933608600210027374181)
        ·
          refine ⟨5912425051612539380132659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31532933608600210027374181 5912425051612539380132659)
          ·
            refine ⟨8868637577418809070198989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912425051612539380132659 8868637577418809070198989)
            ·
              refine ⟨3325739091532053401324621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8868637577418809070198989 3325739091532053401324621)
              ·
                refine ⟨1247152159324520025496733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3325739091532053401324621 1247152159324520025496733)
                ·
                  refine ⟨467682059746695009561275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247152159324520025496733 467682059746695009561275)
                  ·
                    rfl

theorem cell21_2049317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_2049317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049317 prefixEnd_2049317 := by exact prefixLift 2049317
  have htrace : WordTrace (prefixWord ++ tailWord_2049317) baseStart_2049317 baseEnd_2049317 := by
    simpa [prefixWord, tailWord_2049317, baseEnd_2049317] using wordTrace_append hprefix tailTrace_2049317
  have hstable : (prefixWord ++ tailWord_2049317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049317).length < 2 ^ (prefixWord ++ tailWord_2049317).sum := by decide
  have hdescent : baseEnd_2049317 < baseStart_2049317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049345 : List Nat := [1, 2, 5, 2, 1, 1, 1, 8]
def baseStart_2049345 : Nat := 118140960795 + 2049345 * 2 ^ 59
def prefixEnd_2049345 : Nat := 4983230072969 + 3 ^ 40 * 2049345 * 2
def baseEnd_2049345 : Nat := 155896149909391061031517

theorem tailTrace_2049345 : CollatzResearch.WordTrace tailWord_2049345 prefixEnd_2049345 155896149909391061031517 := by
  unfold tailWord_2049345
  simp only [CollatzResearch.WordTrace]
  refine ⟨74745752760580540106165489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49830501840387026737443659 74745752760580540106165489)
  ·
    refine ⟨56059314570435405079624117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74745752760580540106165489 56059314570435405079624117)
    ·
      refine ⟨5255560740978319226214761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56059314570435405079624117 5255560740978319226214761)
      ·
        refine ⟨3941670555733739419661071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5255560740978319226214761 3941670555733739419661071)
        ·
          refine ⟨5912505833600609129491607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941670555733739419661071 5912505833600609129491607)
          ·
            refine ⟨8868758750400913694237411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912505833600609129491607 8868758750400913694237411)
            ·
              refine ⟨13303138125601370541356117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8868758750400913694237411 13303138125601370541356117)
              ·
                refine ⟨155896149909391061031517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13303138125601370541356117 155896149909391061031517)
                ·
                  rfl

theorem cell21_2049345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 8].length) (baseStart_2049345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049345 prefixEnd_2049345 := by exact prefixLift 2049345
  have htrace : WordTrace (prefixWord ++ tailWord_2049345) baseStart_2049345 baseEnd_2049345 := by
    simpa [prefixWord, tailWord_2049345, baseEnd_2049345] using wordTrace_append hprefix tailTrace_2049345
  have hstable : (prefixWord ++ tailWord_2049345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049345).length < 2 ^ (prefixWord ++ tailWord_2049345).sum := by decide
  have hdescent : baseEnd_2049345 < baseStart_2049345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049348 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_2049348 : Nat := 118140960795 + 2049348 * 2 ^ 59
def prefixEnd_2049348 : Nat := 4983230072969 + 3 ^ 40 * 2049348 * 2
def baseEnd_2049348 : Nat := 467689134369045844544545

theorem tailTrace_2049348 : CollatzResearch.WordTrace tailWord_2049348 prefixEnd_2049348 467689134369045844544545 := by
  unfold tailWord_2049348
  simp only [CollatzResearch.WordTrace]
  refine ⟨37372931089784835809262349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49830574786379781079016465 37372931089784835809262349)
  ·
    refine ⟨14014849158669313428473381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37372931089784835809262349 14014849158669313428473381)
    ·
      refine ⟨2627784217250496267838759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14014849158669313428473381 2627784217250496267838759)
      ·
        refine ⟨3941676325875744401758139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2627784217250496267838759 3941676325875744401758139)
        ·
          refine ⟨5912514488813616602637209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3941676325875744401758139 5912514488813616602637209)
          ·
            refine ⟨4434385866610212451977907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5912514488813616602637209 4434385866610212451977907)
            ·
              refine ⟨6651578799915318677966861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434385866610212451977907 6651578799915318677966861)
              ·
                refine ⟨2494342049968244504237573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6651578799915318677966861 2494342049968244504237573)
                ·
                  refine ⟨467689134369045844544545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2494342049968244504237573 467689134369045844544545)
                  ·
                    rfl

theorem cell21_2049348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_2049348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049348 prefixEnd_2049348 := by exact prefixLift 2049348
  have htrace : WordTrace (prefixWord ++ tailWord_2049348) baseStart_2049348 baseEnd_2049348 := by
    simpa [prefixWord, tailWord_2049348, baseEnd_2049348] using wordTrace_append hprefix tailTrace_2049348
  have hstable : (prefixWord ++ tailWord_2049348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049348).length < 2 ^ (prefixWord ++ tailWord_2049348).sum := by decide
  have hdescent : baseEnd_2049348 < baseStart_2049348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049393 : List Nat := [1, 2, 2, 2, 1, 2, 6, 2, 3]
def baseStart_2049393 : Nat := 118140960795 + 2049393 * 2 ^ 59
def prefixEnd_2049393 : Nat := 4983230072969 + 3 ^ 40 * 2049393 * 2
def baseEnd_2049393 : Nat := 467699403982135766294453

theorem tailTrace_2049393 : CollatzResearch.WordTrace tailWord_2049393 prefixEnd_2049393 467699403982135766294453 := by
  unfold tailWord_2049393
  simp only [CollatzResearch.WordTrace]
  refine ⟨74747503464406644303912833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49831668976271096202608555 74747503464406644303912833)
  ·
    refine ⟨56060627598304983227934625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74747503464406644303912833 56060627598304983227934625)
    ·
      refine ⟨42045470698728737420950969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56060627598304983227934625 42045470698728737420950969)
      ·
        refine ⟨31534103024046553065713227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42045470698728737420950969 31534103024046553065713227)
        ·
          refine ⟨47301154536069829598569841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31534103024046553065713227 47301154536069829598569841)
          ·
            refine ⟨35475865902052372198927381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47301154536069829598569841 35475865902052372198927381)
            ·
              refine ⟨1662931214158704946824721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35475865902052372198927381 1662931214158704946824721)
              ·
                refine ⟨1247198410619028710118541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1662931214158704946824721 1247198410619028710118541)
                ·
                  refine ⟨467699403982135766294453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247198410619028710118541 467699403982135766294453)
                  ·
                    rfl

theorem cell21_2049393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_2049393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049393 prefixEnd_2049393 := by exact prefixLift 2049393
  have htrace : WordTrace (prefixWord ++ tailWord_2049393) baseStart_2049393 baseEnd_2049393 := by
    simpa [prefixWord, tailWord_2049393, baseEnd_2049393] using wordTrace_append hprefix tailTrace_2049393
  have hstable : (prefixWord ++ tailWord_2049393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049393).length < 2 ^ (prefixWord ++ tailWord_2049393).sum := by decide
  have hdescent : baseEnd_2049393 < baseStart_2049393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049438 : List Nat := [4, 3, 1, 2, 2, 1, 8]
def baseStart_2049438 : Nat := 118140960795 + 2049438 * 2 ^ 59
def prefixEnd_2049438 : Nat := 4983230072969 + 3 ^ 40 * 2049438 * 2
def baseEnd_2049438 : Nat := 51967741510580632004929

theorem tailTrace_2049438 : CollatzResearch.WordTrace tailWord_2049438 prefixEnd_2049438 51967741510580632004929 := by
  unfold tailWord_2049438
  simp only [CollatzResearch.WordTrace]
  refine ⟨9343643093655452123662621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49832763166162411326200645 9343643093655452123662621)
  ·
    refine ⟨3503866160120794546373483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9343643093655452123662621 3503866160120794546373483)
    ·
      refine ⟨5255799240181191819560225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503866160120794546373483 5255799240181191819560225)
      ·
        refine ⟨3941849430135893864670169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5255799240181191819560225 3941849430135893864670169)
        ·
          refine ⟨2956387072601920398502627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3941849430135893864670169 2956387072601920398502627)
          ·
            refine ⟨4434580608902880597753941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2956387072601920398502627 4434580608902880597753941)
            ·
              refine ⟨51967741510580632004929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4434580608902880597753941 51967741510580632004929)
              ·
                rfl

theorem cell21_2049438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 8].length) (baseStart_2049438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049438 prefixEnd_2049438 := by exact prefixLift 2049438
  have htrace : WordTrace (prefixWord ++ tailWord_2049438) baseStart_2049438 baseEnd_2049438 := by
    simpa [prefixWord, tailWord_2049438, baseEnd_2049438] using wordTrace_append hprefix tailTrace_2049438
  have hstable : (prefixWord ++ tailWord_2049438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049438).length < 2 ^ (prefixWord ++ tailWord_2049438).sum := by decide
  have hdescent : baseEnd_2049438 < baseStart_2049438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049452 : List Nat := [2, 2, 1, 1, 1, 1, 6, 4, 3]
def baseStart_2049452 : Nat := 118140960795 + 2049452 * 2 ^ 59
def prefixEnd_2049452 : Nat := 4983230072969 + 3 ^ 40 * 2049452 * 2
def baseEnd_2049452 : Nat := 467712868585964774810999

theorem tailTrace_2049452 : CollatzResearch.WordTrace tailWord_2049452 prefixEnd_2049452 467712868585964774810999 := by
  unfold tailWord_2049452
  simp only [CollatzResearch.WordTrace]
  refine ⟨37374827685596448690155305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49833103580795264920207073 37374827685596448690155305)
  ·
    refine ⟨28031120764197336517616479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37374827685596448690155305 28031120764197336517616479)
    ·
      refine ⟨42046681146296004776424719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28031120764197336517616479 42046681146296004776424719)
      ·
        refine ⟨63070021719444007164637079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42046681146296004776424719 63070021719444007164637079)
        ·
          refine ⟨94605032579166010746955619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63070021719444007164637079 94605032579166010746955619)
          ·
            refine ⟨141907548868749016120433429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94605032579166010746955619 141907548868749016120433429)
            ·
              refine ⟨6651916353222610130645317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141907548868749016120433429 6651916353222610130645317)
              ·
                refine ⟨1247234316229239399495997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6651916353222610130645317 1247234316229239399495997)
                ·
                  refine ⟨467712868585964774810999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247234316229239399495997 467712868585964774810999)
                  ·
                    rfl

theorem cell21_2049452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_2049452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049452 prefixEnd_2049452 := by exact prefixLift 2049452
  have htrace : WordTrace (prefixWord ++ tailWord_2049452) baseStart_2049452 baseEnd_2049452 := by
    simpa [prefixWord, tailWord_2049452, baseEnd_2049452] using wordTrace_append hprefix tailTrace_2049452
  have hstable : (prefixWord ++ tailWord_2049452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049452).length < 2 ^ (prefixWord ++ tailWord_2049452).sum := by decide
  have hdescent : baseEnd_2049452 < baseStart_2049452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049480 : List Nat := [2, 1, 3, 1, 3, 1, 3, 7]
def baseStart_2049480 : Nat := 118140960795 + 2049480 * 2 ^ 59
def prefixEnd_2049480 : Nat := 4983230072969 + 3 ^ 40 * 2049480 * 2
def baseEnd_2049480 : Nat := 155906419522480982781425

theorem tailTrace_2049480 : CollatzResearch.WordTrace tailWord_2049480 prefixEnd_2049480 155906419522480982781425 := by
  unfold tailWord_2049480
  simp only [CollatzResearch.WordTrace]
  refine ⟨37375338307545729081164947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49833784410060972108219929 37375338307545729081164947)
  ·
    refine ⟨56063007461318593621747421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37375338307545729081164947 56063007461318593621747421)
    ·
      refine ⟨21023627797994472608155283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56063007461318593621747421 21023627797994472608155283)
      ·
        refine ⟨31535441696991708912232925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21023627797994472608155283 31535441696991708912232925)
        ·
          refine ⟨11825790636371890842087347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31535441696991708912232925 11825790636371890842087347)
          ·
            refine ⟨17738685954557836263131021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11825790636371890842087347 17738685954557836263131021)
            ·
              refine ⟨6652007232959188598674133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17738685954557836263131021 6652007232959188598674133)
              ·
                refine ⟨155906419522480982781425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6652007232959188598674133 155906419522480982781425)
                ·
                  rfl

theorem cell21_2049480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_2049480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049480 prefixEnd_2049480 := by exact prefixLift 2049480
  have htrace : WordTrace (prefixWord ++ tailWord_2049480) baseStart_2049480 baseEnd_2049480 := by
    simpa [prefixWord, tailWord_2049480, baseEnd_2049480] using wordTrace_append hprefix tailTrace_2049480
  have hstable : (prefixWord ++ tailWord_2049480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049480).length < 2 ^ (prefixWord ++ tailWord_2049480).sum := by decide
  have hdescent : baseEnd_2049480 < baseStart_2049480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049517 : List Nat := [1, 5, 1, 3, 2, 2, 2, 1, 4]
def baseStart_2049517 : Nat := 118140960795 + 2049517 * 2 ^ 59
def prefixEnd_2049517 : Nat := 4983230072969 + 3 ^ 40 * 2049517 * 2
def baseEnd_2049517 : Nat := 467727702471539106227533

theorem tailTrace_2049517 : CollatzResearch.WordTrace tailWord_2049517 prefixEnd_2049517 467727702471539106227533 := by
  unfold tailWord_2049517
  simp only [CollatzResearch.WordTrace]
  refine ⟨74752026115957413481426805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49834684077304942320951203 74752026115957413481426805)
  ·
    refine ⟨7008002448371007513883763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74752026115957413481426805 7008002448371007513883763)
    ·
      refine ⟨10512003672556511270825645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7008002448371007513883763 10512003672556511270825645)
      ·
        refine ⟨3942001377208691726559617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10512003672556511270825645 3942001377208691726559617)
        ·
          refine ⟨2956501032906518794919713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3942001377208691726559617 2956501032906518794919713)
          ·
            refine ⟨2217375774679889096189785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2956501032906518794919713 2217375774679889096189785)
            ·
              refine ⟨1663031831009916822142339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217375774679889096189785 1663031831009916822142339)
              ·
                refine ⟨2494547746514875233213509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663031831009916822142339 2494547746514875233213509)
                ·
                  refine ⟨467727702471539106227533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2494547746514875233213509 467727702471539106227533)
                  ·
                    rfl

theorem cell21_2049517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_2049517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049517 prefixEnd_2049517 := by exact prefixLift 2049517
  have htrace : WordTrace (prefixWord ++ tailWord_2049517) baseStart_2049517 baseEnd_2049517 := by
    simpa [prefixWord, tailWord_2049517, baseEnd_2049517] using wordTrace_append hprefix tailTrace_2049517
  have hstable : (prefixWord ++ tailWord_2049517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049517).length < 2 ^ (prefixWord ++ tailWord_2049517).sum := by decide
  have hdescent : baseEnd_2049517 < baseStart_2049517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049587 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 5]
def baseStart_2049587 : Nat := 118140960795 + 2049587 * 2 ^ 59
def prefixEnd_2049587 : Nat := 4983230072969 + 3 ^ 40 * 2049587 * 2
def baseEnd_2049587 : Nat := 467743677425234540060723

theorem tailTrace_2049587 : CollatzResearch.WordTrace tailWord_2049587 prefixEnd_2049587 467743677425234540060723 := by
  unfold tailWord_2049587
  simp only [CollatzResearch.WordTrace]
  refine ⟨74754579225703815436475015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49836386150469210290983343 74754579225703815436475015)
  ·
    refine ⟨112131868838555723154712523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74754579225703815436475015 112131868838555723154712523)
    ·
      refine ⟨168197803257833584732068785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112131868838555723154712523 168197803257833584732068785)
      ·
        refine ⟨126148352443375188549051589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168197803257833584732068785 126148352443375188549051589)
        ·
          refine ⟨23652816083132847852947173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126148352443375188549051589 23652816083132847852947173)
          ·
            refine ⟨4434903015587408972427595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23652816083132847852947173 4434903015587408972427595)
            ·
              refine ⟨6652354523381113458641393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434903015587408972427595 6652354523381113458641393)
              ·
                refine ⟨4989265892535835093981045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6652354523381113458641393 4989265892535835093981045)
                ·
                  refine ⟨467743677425234540060723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4989265892535835093981045 467743677425234540060723)
                  ·
                    rfl

theorem cell21_2049587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_2049587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049587 prefixEnd_2049587 := by exact prefixLift 2049587
  have htrace : WordTrace (prefixWord ++ tailWord_2049587) baseStart_2049587 baseEnd_2049587 := by
    simpa [prefixWord, tailWord_2049587, baseEnd_2049587] using wordTrace_append hprefix tailTrace_2049587
  have hstable : (prefixWord ++ tailWord_2049587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049587).length < 2 ^ (prefixWord ++ tailWord_2049587).sum := by decide
  have hdescent : baseEnd_2049587 < baseStart_2049587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049618 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_2049618 : Nat := 118140960795 + 2049618 * 2 ^ 59
def prefixEnd_2049618 : Nat := 4983230072969 + 3 ^ 40 * 2049618 * 2
def baseEnd_2049618 : Nat := 467750752047585375043993

theorem tailTrace_2049618 : CollatzResearch.WordTrace tailWord_2049618 prefixEnd_2049618 467750752047585375043993 := by
  unfold tailWord_2049618
  simp only [CollatzResearch.WordTrace]
  refine ⟨18688927472147876932713377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49837139925727671820569005 18688927472147876932713377)
  ·
    refine ⟨14016695604110907699535033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18688927472147876932713377 14016695604110907699535033)
    ·
      refine ⟨10512521703083180774651275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14016695604110907699535033 10512521703083180774651275)
      ·
        refine ⟨15768782554624771161976913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512521703083180774651275 15768782554624771161976913)
        ·
          refine ⟨11826586915968578371482685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15768782554624771161976913 11826586915968578371482685)
          ·
            refine ⟨4434970093488216889306007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11826586915968578371482685 4434970093488216889306007)
            ·
              refine ⟨6652455140232325333959011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4434970093488216889306007 6652455140232325333959011)
              ·
                refine ⟨9978682710348488000938517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652455140232325333959011 9978682710348488000938517)
                ·
                  refine ⟨467750752047585375043993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9978682710348488000938517 467750752047585375043993)
                  ·
                    rfl

theorem cell21_2049618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_2049618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049618 prefixEnd_2049618 := by exact prefixLift 2049618
  have htrace : WordTrace (prefixWord ++ tailWord_2049618) baseStart_2049618 baseEnd_2049618 := by
    simpa [prefixWord, tailWord_2049618, baseEnd_2049618] using wordTrace_append hprefix tailTrace_2049618
  have hstable : (prefixWord ++ tailWord_2049618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049618).length < 2 ^ (prefixWord ++ tailWord_2049618).sum := by decide
  have hdescent : baseEnd_2049618 < baseStart_2049618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049635 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 4]
def baseStart_2049635 : Nat := 118140960795 + 2049635 * 2 ^ 59
def prefixEnd_2049635 : Nat := 4983230072969 + 3 ^ 40 * 2049635 * 2
def baseEnd_2049635 : Nat := 467754631679197123260625

theorem tailTrace_2049635 : CollatzResearch.WordTrace tailWord_2049635 prefixEnd_2049635 467754631679197123260625 := by
  unfold tailWord_2049635
  simp only [CollatzResearch.WordTrace]
  refine ⟨74756329929529919634222359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49837553286353279756148239 74756329929529919634222359)
  ·
    refine ⟨112134494894294879451333539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74756329929529919634222359 112134494894294879451333539)
    ·
      refine ⟨168201742341442319177000309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112134494894294879451333539 168201742341442319177000309)
      ·
        refine ⟨15768913344510217422843779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168201742341442319177000309 15768913344510217422843779)
        ·
          refine ⟨23653370016765326134265669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15768913344510217422843779 23653370016765326134265669)
          ·
            refine ⟨4435006878143498650174813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23653370016765326134265669 4435006878143498650174813)
            ·
              refine ⟨1663127579303811993815555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4435006878143498650174813 1663127579303811993815555)
              ·
                refine ⟨2494691368955717990723333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663127579303811993815555 2494691368955717990723333)
                ·
                  refine ⟨467754631679197123260625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2494691368955717990723333 467754631679197123260625)
                  ·
                    rfl

theorem cell21_2049635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 4].length) (baseStart_2049635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049635 prefixEnd_2049635 := by exact prefixLift 2049635
  have htrace : WordTrace (prefixWord ++ tailWord_2049635) baseStart_2049635 baseEnd_2049635 := by
    simpa [prefixWord, tailWord_2049635, baseEnd_2049635] using wordTrace_append hprefix tailTrace_2049635
  have hstable : (prefixWord ++ tailWord_2049635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049635).length < 2 ^ (prefixWord ++ tailWord_2049635).sum := by decide
  have hdescent : baseEnd_2049635 < baseStart_2049635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049773 : List Nat := [1, 5, 1, 2, 1, 3, 2, 3, 3]
def baseStart_2049773 : Nat := 118140960795 + 2049773 * 2 ^ 59
def prefixEnd_2049773 : Nat := 4983230072969 + 3 ^ 40 * 2049773 * 2
def baseEnd_2049773 : Nat := 467786125159339549960343

theorem tailTrace_2049773 : CollatzResearch.WordTrace tailWord_2049773 prefixEnd_2049773 467786125159339549960343 := by
  unfold tailWord_2049773
  simp only [CollatzResearch.WordTrace]
  refine ⟨74761363203029969202745973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49840908802019979468497315 74761363203029969202745973)
  ·
    refine ⟨7008877800284059612757435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74761363203029969202745973 7008877800284059612757435)
    ·
      refine ⟨10513316700426089419136153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7008877800284059612757435 10513316700426089419136153)
      ·
        refine ⟨7884987525319567064352115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10513316700426089419136153 7884987525319567064352115)
        ·
          refine ⟨11827481287979350596528173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7884987525319567064352115 11827481287979350596528173)
          ·
            refine ⟨4435305482992256473698065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11827481287979350596528173 4435305482992256473698065)
            ·
              refine ⟨3326479112244192355273549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4435305482992256473698065 3326479112244192355273549)
              ·
                refine ⟨1247429667091572133227581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3326479112244192355273549 1247429667091572133227581)
                ·
                  refine ⟨467786125159339549960343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247429667091572133227581 467786125159339549960343)
                  ·
                    rfl

theorem cell21_2049773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_2049773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049773 prefixEnd_2049773 := by exact prefixLift 2049773
  have htrace : WordTrace (prefixWord ++ tailWord_2049773) baseStart_2049773 baseEnd_2049773 := by
    simpa [prefixWord, tailWord_2049773, baseEnd_2049773] using wordTrace_append hprefix tailTrace_2049773
  have hstable : (prefixWord ++ tailWord_2049773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049773).length < 2 ^ (prefixWord ++ tailWord_2049773).sum := by decide
  have hdescent : baseEnd_2049773 < baseStart_2049773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049815 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 5]
def baseStart_2049815 : Nat := 118140960795 + 2049815 * 2 ^ 59
def prefixEnd_2049815 : Nat := 4983230072969 + 3 ^ 40 * 2049815 * 2
def baseEnd_2049815 : Nat := 467795710131556810260257

theorem tailTrace_2049815 : CollatzResearch.WordTrace tailWord_2049815 prefixEnd_2049815 467795710131556810260257 := by
  unfold tailWord_2049815
  simp only [CollatzResearch.WordTrace]
  refine ⟨74762895068877810375774899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49841930045918540250516599 74762895068877810375774899)
  ·
    refine ⟨112144342603316715563662349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74762895068877810375774899 112144342603316715563662349)
    ·
      refine ⟨42054128476243768336373381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112144342603316715563662349 42054128476243768336373381)
      ·
        refine ⟨7885149089295706563070009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42054128476243768336373381 7885149089295706563070009)
        ·
          refine ⟨5913861816971779922302507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7885149089295706563070009 5913861816971779922302507)
          ·
            refine ⟨8870792725457669883453761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5913861816971779922302507 8870792725457669883453761)
            ·
              refine ⟨6653094544093252412590321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8870792725457669883453761 6653094544093252412590321)
              ·
                refine ⟨4989820908069939309442741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653094544093252412590321 4989820908069939309442741)
                ·
                  refine ⟨467795710131556810260257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4989820908069939309442741 467795710131556810260257)
                  ·
                    rfl

theorem cell21_2049815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_2049815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049815 prefixEnd_2049815 := by exact prefixLift 2049815
  have htrace : WordTrace (prefixWord ++ tailWord_2049815) baseStart_2049815 baseEnd_2049815 := by
    simpa [prefixWord, tailWord_2049815, baseEnd_2049815] using wordTrace_append hprefix tailTrace_2049815
  have hstable : (prefixWord ++ tailWord_2049815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049815).length < 2 ^ (prefixWord ++ tailWord_2049815).sum := by decide
  have hdescent : baseEnd_2049815 < baseStart_2049815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049829 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 6]
def baseStart_2049829 : Nat := 118140960795 + 2049829 * 2 ^ 59
def prefixEnd_2049829 : Nat := 4983230072969 + 3 ^ 40 * 2049829 * 2
def baseEnd_2049829 : Nat := 467798905122295897026895

theorem tailTrace_2049829 : CollatzResearch.WordTrace tailWord_2049829 prefixEnd_2049829 467798905122295897026895 := by
  unfold tailWord_2049829
  simp only [CollatzResearch.WordTrace]
  refine ⟨74763405690827090766784541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49842270460551393844523027 74763405690827090766784541)
  ·
    refine ⟨28036277134060159037544203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74763405690827090766784541 28036277134060159037544203)
    ·
      refine ⟨42054415701090238556316305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28036277134060159037544203 42054415701090238556316305)
      ·
        refine ⟨31540811775817678917237229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42054415701090238556316305 31540811775817678917237229)
        ·
          refine ⟨11827804415931629593963961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31540811775817678917237229 11827804415931629593963961)
          ·
            refine ⟨8870853311948722195472971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11827804415931629593963961 8870853311948722195472971)
            ·
              refine ⟨13306279967923083293209457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8870853311948722195472971 13306279967923083293209457)
              ·
                refine ⟨9979709975942312469907093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13306279967923083293209457 9979709975942312469907093)
                ·
                  refine ⟨467798905122295897026895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9979709975942312469907093 467798905122295897026895)
                  ·
                    rfl

theorem cell21_2049829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_2049829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049829 prefixEnd_2049829 := by exact prefixLift 2049829
  have htrace : WordTrace (prefixWord ++ tailWord_2049829) baseStart_2049829 baseEnd_2049829 := by
    simpa [prefixWord, tailWord_2049829, baseEnd_2049829] using wordTrace_append hprefix tailTrace_2049829
  have hstable : (prefixWord ++ tailWord_2049829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049829).length < 2 ^ (prefixWord ++ tailWord_2049829).sum := by decide
  have hdescent : baseEnd_2049829 < baseStart_2049829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049849 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 5]
def baseStart_2049849 : Nat := 118140960795 + 2049849 * 2 ^ 59
def prefixEnd_2049849 : Nat := 4983230072969 + 3 ^ 40 * 2049849 * 2
def baseEnd_2049849 : Nat := 467803469394780306693521

theorem tailTrace_2049849 : CollatzResearch.WordTrace tailWord_2049849 prefixEnd_2049849 467803469394780306693521 := by
  unfold tailWord_2049849
  simp only [CollatzResearch.WordTrace]
  refine ⟨74764135150754634182512601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49842756767169756121675067 74764135150754634182512601)
  ·
    refine ⟨56073101363065975636884451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74764135150754634182512601 56073101363065975636884451)
    ·
      refine ⟨84109652044598963455326677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56073101363065975636884451 84109652044598963455326677)
      ·
        refine ⟨1971319969795288205984219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 84109652044598963455326677 1971319969795288205984219)
        ·
          refine ⟨2956979954692932308976329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1971319969795288205984219 2956979954692932308976329)
          ·
            refine ⟨2217734966019699231732247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2956979954692932308976329 2217734966019699231732247)
            ·
              refine ⟨3326602449029548847598371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217734966019699231732247 3326602449029548847598371)
              ·
                refine ⟨4989903673544323271397557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326602449029548847598371 4989903673544323271397557)
                ·
                  refine ⟨467803469394780306693521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4989903673544323271397557 467803469394780306693521)
                  ·
                    rfl

theorem cell21_2049849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_2049849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049849 prefixEnd_2049849 := by exact prefixLift 2049849
  have htrace : WordTrace (prefixWord ++ tailWord_2049849) baseStart_2049849 baseEnd_2049849 := by
    simpa [prefixWord, tailWord_2049849, baseEnd_2049849] using wordTrace_append hprefix tailTrace_2049849
  have hstable : (prefixWord ++ tailWord_2049849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049849).length < 2 ^ (prefixWord ++ tailWord_2049849).sum := by decide
  have hdescent : baseEnd_2049849 < baseStart_2049849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049967 : List Nat := [1, 1, 2, 1, 2, 2, 3, 6, 3]
def baseStart_2049967 : Nat := 118140960795 + 2049967 * 2 ^ 59
def prefixEnd_2049967 : Nat := 4983230072969 + 3 ^ 40 * 2049967 * 2
def baseEnd_2049967 : Nat := 467830398602438323726613

theorem tailTrace_2049967 : CollatzResearch.WordTrace tailWord_2049967 prefixEnd_2049967 467830398602438323726613 := by
  unfold tailWord_2049967
  simp only [CollatzResearch.WordTrace]
  refine ⟨74768438964327140335308155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49845625976218093556872103 74768438964327140335308155)
  ·
    refine ⟨112152658446490710502962233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74768438964327140335308155 112152658446490710502962233)
    ·
      refine ⟨84114493834868032877221675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112152658446490710502962233 84114493834868032877221675)
      ·
        refine ⟨126171740752302049315832513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84114493834868032877221675 126171740752302049315832513)
        ·
          refine ⟨94628805564226536986874385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126171740752302049315832513 94628805564226536986874385)
          ·
            refine ⟨70971604173169902740155789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94628805564226536986874385 70971604173169902740155789)
            ·
              refine ⟨26614351564938713527558421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70971604173169902740155789 26614351564938713527558421)
              ·
                refine ⟨1247547729606502196604301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26614351564938713527558421 1247547729606502196604301)
                ·
                  refine ⟨467830398602438323726613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247547729606502196604301 467830398602438323726613)
                  ·
                    rfl

theorem cell21_2049967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 6, 3].length) (baseStart_2049967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049967 prefixEnd_2049967 := by exact prefixLift 2049967
  have htrace : WordTrace (prefixWord ++ tailWord_2049967) baseStart_2049967 baseEnd_2049967 := by
    simpa [prefixWord, tailWord_2049967, baseEnd_2049967] using wordTrace_append hprefix tailTrace_2049967
  have hstable : (prefixWord ++ tailWord_2049967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049967).length < 2 ^ (prefixWord ++ tailWord_2049967).sum := by decide
  have hdescent : baseEnd_2049967 < baseStart_2049967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2049995 : List Nat := [1, 1, 1, 1, 3, 4, 3, 7]
def baseStart_2049995 : Nat := 118140960795 + 2049995 * 2 ^ 59
def prefixEnd_2049995 : Nat := 4983230072969 + 3 ^ 40 * 2049995 * 2
def baseEnd_2049995 : Nat := 155945596194638832419963

theorem tailTrace_2049995 : CollatzResearch.WordTrace tailWord_2049995 prefixEnd_2049995 155945596194638832419963 := by
  unfold tailWord_2049995
  simp only [CollatzResearch.WordTrace]
  refine ⟨74769460208225701117327439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49846306805483800744884959 74769460208225701117327439)
  ·
    refine ⟨112154190312338551675991159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74769460208225701117327439 112154190312338551675991159)
    ·
      refine ⟨168231285468507827513986739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112154190312338551675991159 168231285468507827513986739)
      ·
        refine ⟨252346928202761741270980109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168231285468507827513986739 252346928202761741270980109)
        ·
          refine ⟨94630098076035652976617541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252346928202761741270980109 94630098076035652976617541)
          ·
            refine ⟨17743143389256684933115789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94630098076035652976617541 17743143389256684933115789)
            ·
              refine ⟨6653678770971256849918421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17743143389256684933115789 6653678770971256849918421)
              ·
                refine ⟨155945596194638832419963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6653678770971256849918421 155945596194638832419963)
                ·
                  rfl

theorem cell21_2049995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 7].length) (baseStart_2049995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2049995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2049995 prefixEnd_2049995 := by exact prefixLift 2049995
  have htrace : WordTrace (prefixWord ++ tailWord_2049995) baseStart_2049995 baseEnd_2049995 := by
    simpa [prefixWord, tailWord_2049995, baseEnd_2049995] using wordTrace_append hprefix tailTrace_2049995
  have hstable : (prefixWord ++ tailWord_2049995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2049995).length < 2 ^ (prefixWord ++ tailWord_2049995).sum := by decide
  have hdescent : baseEnd_2049995 < baseStart_2049995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2049995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050018 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_2050018 : Nat := 118140960795 + 2050018 * 2 ^ 59
def prefixEnd_2050018 : Nat := 4983230072969 + 3 ^ 40 * 2050018 * 2
def baseEnd_2050018 : Nat := 467842037497273568376509

theorem tailTrace_2050018 : CollatzResearch.WordTrace tailWord_2050018 prefixEnd_2050018 467842037497273568376509 := by
  unfold tailWord_2050018
  simp only [CollatzResearch.WordTrace]
  refine ⟨18692574771785594011353677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49846866058094917363609805 18692574771785594011353677)
  ·
    refine ⟨7009715539419597754257629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18692574771785594011353677 7009715539419597754257629)
    ·
      refine ⟨2628643327282349157846611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7009715539419597754257629 2628643327282349157846611)
      ·
        refine ⟨3942964990923523736769917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628643327282349157846611 3942964990923523736769917)
        ·
          refine ⟨1478611871596321401288719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3942964990923523736769917 1478611871596321401288719)
          ·
            refine ⟨2217917807394482101933079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478611871596321401288719 2217917807394482101933079)
            ·
              refine ⟨3326876711091723152899619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2217917807394482101933079 3326876711091723152899619)
              ·
                refine ⟨4990315066637584729349429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326876711091723152899619 4990315066637584729349429)
                ·
                  refine ⟨467842037497273568376509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4990315066637584729349429 467842037497273568376509)
                  ·
                    rfl

theorem cell21_2050018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_2050018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050018 prefixEnd_2050018 := by exact prefixLift 2050018
  have htrace : WordTrace (prefixWord ++ tailWord_2050018) baseStart_2050018 baseEnd_2050018 := by
    simpa [prefixWord, tailWord_2050018, baseEnd_2050018] using wordTrace_append hprefix tailTrace_2050018
  have hstable : (prefixWord ++ tailWord_2050018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050018).length < 2 ^ (prefixWord ++ tailWord_2050018).sum := by decide
  have hdescent : baseEnd_2050018 < baseStart_2050018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050071 : List Nat := [1, 1, 3, 5, 11]
def baseStart_2050071 : Nat := 118140960795 + 2050071 * 2 ^ 59
def prefixEnd_2050071 : Nat := 4983230072969 + 3 ^ 40 * 2050071 * 2
def baseEnd_2050071 : Nat := 5775976948387126592507

theorem tailTrace_2050071 : CollatzResearch.WordTrace tailWord_2050071 prefixEnd_2050071 5775976948387126592507 := by
  unfold tailWord_2050071
  simp only [CollatzResearch.WordTrace]
  refine ⟨74772232155950366097094067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49848154770633577398062711 74772232155950366097094067)
  ·
    refine ⟨112158348233925549145641101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74772232155950366097094067 112158348233925549145641101)
    ·
      refine ⟨42059380587722080929615413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112158348233925549145641101 42059380587722080929615413)
      ·
        refine ⟨3943066930098945087151445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42059380587722080929615413 3943066930098945087151445)
        ·
          refine ⟨5775976948387126592507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3943066930098945087151445 5775976948387126592507)
          ·
            rfl

theorem cell21_2050071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 11].length) (baseStart_2050071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050071 prefixEnd_2050071 := by exact prefixLift 2050071
  have htrace : WordTrace (prefixWord ++ tailWord_2050071) baseStart_2050071 baseEnd_2050071 := by
    simpa [prefixWord, tailWord_2050071, baseEnd_2050071] using wordTrace_append hprefix tailTrace_2050071
  have hstable : (prefixWord ++ tailWord_2050071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050071).length < 2 ^ (prefixWord ++ tailWord_2050071).sum := by decide
  have hdescent : baseEnd_2050071 < baseStart_2050071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050074 : List Nat := [3, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_2050074 : Nat := 118140960795 + 2050074 * 2 ^ 59
def prefixEnd_2050074 : Nat := 4983230072969 + 3 ^ 40 * 2050074 * 2
def baseEnd_2050074 : Nat := 467854817460229915443061

theorem tailTrace_2050074 : CollatzResearch.WordTrace tailWord_2050074 prefixEnd_2050074 467854817460229915443061 := by
  unfold tailWord_2050074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18693085393734874402363319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49848227716626331739635517 18693085393734874402363319)
  ·
    refine ⟨28039628090602311603544979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18693085393734874402363319 28039628090602311603544979)
    ·
      refine ⟨42059442135903467405317469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28039628090602311603544979 42059442135903467405317469)
      ·
        refine ⟨15772290800963800276994051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42059442135903467405317469 15772290800963800276994051)
        ·
          refine ⟨23658436201445700415491077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15772290800963800276994051 23658436201445700415491077)
          ·
            refine ⟨4435956787771068827904577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23658436201445700415491077 4435956787771068827904577)
            ·
              refine ⟨3326967590828301620928433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4435956787771068827904577 3326967590828301620928433)
              ·
                refine ⟨2495225693121226215696325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3326967590828301620928433 2495225693121226215696325)
                ·
                  refine ⟨467854817460229915443061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495225693121226215696325 467854817460229915443061)
                  ·
                    rfl

theorem cell21_2050074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_2050074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050074 prefixEnd_2050074 := by exact prefixLift 2050074
  have htrace : WordTrace (prefixWord ++ tailWord_2050074) baseStart_2050074 baseEnd_2050074 := by
    simpa [prefixWord, tailWord_2050074, baseEnd_2050074] using wordTrace_append hprefix tailTrace_2050074
  have hstable : (prefixWord ++ tailWord_2050074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050074).length < 2 ^ (prefixWord ++ tailWord_2050074).sum := by decide
  have hdescent : baseEnd_2050074 < baseStart_2050074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050077 : List Nat := [1, 4, 2, 2, 2, 1, 4, 2, 3]
def baseStart_2050077 : Nat := 118140960795 + 2050077 * 2 ^ 59
def prefixEnd_2050077 : Nat := 4983230072969 + 3 ^ 40 * 2050077 * 2
def baseEnd_2050077 : Nat := 467855502101102576893055

theorem tailTrace_2050077 : CollatzResearch.WordTrace tailWord_2050077 prefixEnd_2050077 467855502101102576893055 := by
  unfold tailWord_2050077
  simp only [CollatzResearch.WordTrace]
  refine ⟨74772450993928629121812485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49848300662619086081208323 74772450993928629121812485)
  ·
    refine ⟨14019834561361617960339841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74772450993928629121812485 14019834561361617960339841)
    ·
      refine ⟨10514875921021213470254881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14019834561361617960339841 10514875921021213470254881)
      ·
        refine ⟨7886156940765910102691161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10514875921021213470254881 7886156940765910102691161)
        ·
          refine ⟨5914617705574432577018371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7886156940765910102691161 5914617705574432577018371)
          ·
            refine ⟨8871926558361648865527557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914617705574432577018371 8871926558361648865527557)
            ·
              refine ⟨1663486229692809162286417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8871926558361648865527557 1663486229692809162286417)
              ·
                refine ⟨1247614672269606871714813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663486229692809162286417 1247614672269606871714813)
                ·
                  refine ⟨467855502101102576893055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247614672269606871714813 467855502101102576893055)
                  ·
                    rfl

theorem cell21_2050077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_2050077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050077 prefixEnd_2050077 := by exact prefixLift 2050077
  have htrace : WordTrace (prefixWord ++ tailWord_2050077) baseStart_2050077 baseEnd_2050077 := by
    simpa [prefixWord, tailWord_2050077, baseEnd_2050077] using wordTrace_append hprefix tailTrace_2050077
  have hstable : (prefixWord ++ tailWord_2050077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050077).length < 2 ^ (prefixWord ++ tailWord_2050077).sum := by decide
  have hdescent : baseEnd_2050077 < baseStart_2050077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050105 : List Nat := [1, 2, 1, 5, 3, 1, 3, 5]
def baseStart_2050105 : Nat := 118140960795 + 2050105 * 2 ^ 59
def prefixEnd_2050105 : Nat := 4983230072969 + 3 ^ 40 * 2050105 * 2
def baseEnd_2050105 : Nat := 155953964027526916808777

theorem tailTrace_2050105 : CollatzResearch.WordTrace tailWord_2050105 prefixEnd_2050105 155953964027526916808777 := by
  unfold tailWord_2050105
  simp only [CollatzResearch.WordTrace]
  refine ⟨74773472237827189903831769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49848981491884793269221179 74773472237827189903831769)
  ·
    refine ⟨56080104178370392427873827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74773472237827189903831769 56080104178370392427873827)
    ·
      refine ⟨84120156267555588641810741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56080104178370392427873827 84120156267555588641810741)
      ·
        refine ⟨7886264650083336435169757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84120156267555588641810741 7886264650083336435169757)
        ·
          refine ⟨2957349243781251163188659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7886264650083336435169757 2957349243781251163188659)
          ·
            refine ⟨4436023865671876744782989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957349243781251163188659 4436023865671876744782989)
            ·
              refine ⟨1663508949626953779293621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4436023865671876744782989 1663508949626953779293621)
              ·
                refine ⟨155953964027526916808777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1663508949626953779293621 155953964027526916808777)
                ·
                  rfl

theorem cell21_2050105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 5].length) (baseStart_2050105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050105 prefixEnd_2050105 := by exact prefixLift 2050105
  have htrace : WordTrace (prefixWord ++ tailWord_2050105) baseStart_2050105 baseEnd_2050105 := by
    simpa [prefixWord, tailWord_2050105, baseEnd_2050105] using wordTrace_append hprefix tailTrace_2050105
  have hstable : (prefixWord ++ tailWord_2050105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050105).length < 2 ^ (prefixWord ++ tailWord_2050105).sum := by decide
  have hdescent : baseEnd_2050105 < baseStart_2050105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050133 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 6]
def baseStart_2050133 : Nat := 118140960795 + 2050133 * 2 ^ 59
def prefixEnd_2050133 : Nat := 4983230072969 + 3 ^ 40 * 2050133 * 2
def baseEnd_2050133 : Nat := 467868282064058923959607

theorem tailTrace_2050133 : CollatzResearch.WordTrace tailWord_2050133 prefixEnd_2050133 467868282064058923959607 := by
  unfold tailWord_2050133
  simp only [CollatzResearch.WordTrace]
  refine ⟨74774493481725750685851053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49849662321150500457234035 74774493481725750685851053)
  ·
    refine ⟨28040435055647156507194145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74774493481725750685851053 28040435055647156507194145)
    ·
      refine ⟨21030326291735367380395609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28040435055647156507194145 21030326291735367380395609)
      ·
        refine ⟨15772744718801525535296707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21030326291735367380395609 15772744718801525535296707)
        ·
          refine ⟨23659117078202288302945061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15772744718801525535296707 23659117078202288302945061)
          ·
            refine ⟨4436084452162929056802199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23659117078202288302945061 4436084452162929056802199)
            ·
              refine ⟨6654126678244393585203299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436084452162929056802199 6654126678244393585203299)
              ·
                refine ⟨9981190017366590377804949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654126678244393585203299 9981190017366590377804949)
                ·
                  refine ⟨467868282064058923959607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9981190017366590377804949 467868282064058923959607)
                  ·
                    rfl

theorem cell21_2050133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_2050133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050133 prefixEnd_2050133 := by exact prefixLift 2050133
  have htrace : WordTrace (prefixWord ++ tailWord_2050133) baseStart_2050133 baseEnd_2050133 := by
    simpa [prefixWord, tailWord_2050133, baseEnd_2050133] using wordTrace_append hprefix tailTrace_2050133
  have hstable : (prefixWord ++ tailWord_2050133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050133).length < 2 ^ (prefixWord ++ tailWord_2050133).sum := by decide
  have hdescent : baseEnd_2050133 < baseStart_2050133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050192 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_2050192 : Nat := 118140960795 + 2050192 * 2 ^ 59
def prefixEnd_2050192 : Nat := 4983230072969 + 3 ^ 40 * 2050192 * 2
def baseEnd_2050192 : Nat := 467881746667887932476153

theorem tailTrace_2050192 : CollatzResearch.WordTrace tailWord_2050192 prefixEnd_2050192 467881746667887932476153 := by
  unfold tailWord_2050192
  simp only [CollatzResearch.WordTrace]
  refine ⟨37388322694256001881124415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49851096925674669174832553 37388322694256001881124415)
  ·
    refine ⟨56082484041384002821686623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37388322694256001881124415 56082484041384002821686623)
    ·
      refine ⟨84123726062076004232529935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56082484041384002821686623 84123726062076004232529935)
      ·
        refine ⟨126185589093114006348794903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84123726062076004232529935 126185589093114006348794903)
        ·
          refine ⟨189278383639671009523192355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126185589093114006348794903 189278383639671009523192355)
          ·
            refine ⟨283917575459506514284788533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189278383639671009523192355 283917575459506514284788533)
            ·
              refine ⟨26617272699328735714198925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283917575459506514284788533 26617272699328735714198925)
              ·
                refine ⟨9981477262248275892824597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26617272699328735714198925 9981477262248275892824597)
                ·
                  refine ⟨467881746667887932476153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9981477262248275892824597 467881746667887932476153)
                  ·
                    rfl

theorem cell21_2050192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_2050192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050192 prefixEnd_2050192 := by exact prefixLift 2050192
  have htrace : WordTrace (prefixWord ++ tailWord_2050192) baseStart_2050192 baseEnd_2050192 := by
    simpa [prefixWord, tailWord_2050192, baseEnd_2050192] using wordTrace_append hprefix tailTrace_2050192
  have hstable : (prefixWord ++ tailWord_2050192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050192).length < 2 ^ (prefixWord ++ tailWord_2050192).sum := by decide
  have hdescent : baseEnd_2050192 < baseStart_2050192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050350 : List Nat := [4, 1, 3, 3, 2, 1, 7]
def baseStart_2050350 : Nat := 118140960795 + 2050350 * 2 ^ 59
def prefixEnd_2050350 : Nat := 4983230072969 + 3 ^ 40 * 2050350 * 2
def baseEnd_2050350 : Nat := 51990867157834974315833

theorem tailTrace_2050350 : CollatzResearch.WordTrace tailWord_2050350 prefixEnd_2050350 51990867157834974315833 := by
  unfold tailWord_2050350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347801015242449593312563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49854938747959731164333669 9347801015242449593312563)
  ·
    refine ⟨14021701522863674389968845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9347801015242449593312563 14021701522863674389968845)
    ·
      refine ⟨5258138071073877896238317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14021701522863674389968845 5258138071073877896238317)
      ·
        refine ⟨1971801776652704211089369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5258138071073877896238317 1971801776652704211089369)
        ·
          refine ⟨1478851332489528158317027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1971801776652704211089369 1478851332489528158317027)
          ·
            refine ⟨2218276998734292237475541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1478851332489528158317027 2218276998734292237475541)
            ·
              refine ⟨51990867157834974315833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2218276998734292237475541 51990867157834974315833)
              ·
                rfl

theorem cell21_2050350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 7].length) (baseStart_2050350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050350 prefixEnd_2050350 := by exact prefixLift 2050350
  have htrace : WordTrace (prefixWord ++ tailWord_2050350) baseStart_2050350 baseEnd_2050350 := by
    simpa [prefixWord, tailWord_2050350, baseEnd_2050350] using wordTrace_append hprefix tailTrace_2050350
  have hstable : (prefixWord ++ tailWord_2050350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050350).length < 2 ^ (prefixWord ++ tailWord_2050350).sum := by decide
  have hdescent : baseEnd_2050350 < baseStart_2050350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050361 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 6]
def baseStart_2050361 : Nat := 118140960795 + 2050361 * 2 ^ 59
def prefixEnd_2050361 : Nat := 4983230072969 + 3 ^ 40 * 2050361 * 2
def baseEnd_2050361 : Nat := 467920314770381194159141

theorem tailTrace_2050361 : CollatzResearch.WordTrace tailWord_2050361 prefixEnd_2050361 467920314770381194159141 := by
  unfold tailWord_2050361
  simp only [CollatzResearch.WordTrace]
  refine ⟨74782809324899745625150937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49855206216599830416767291 74782809324899745625150937)
  ·
    refine ⟨56087106993674809218863203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74782809324899745625150937 56087106993674809218863203)
    ·
      refine ⟨84130660490512213828294805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56087106993674809218863203 84130660490512213828294805)
      ·
        refine ⟨3943624710492760023201319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84130660490512213828294805 3943624710492760023201319)
        ·
          refine ⟨5915437065739140034801979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943624710492760023201319 5915437065739140034801979)
          ·
            refine ⟨8873155598608710052202969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915437065739140034801979 8873155598608710052202969)
            ·
              refine ⟨6654866698956532539152227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8873155598608710052202969 6654866698956532539152227)
              ·
                refine ⟨9982300048434798808728341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654866698956532539152227 9982300048434798808728341)
                ·
                  refine ⟨467920314770381194159141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9982300048434798808728341 467920314770381194159141)
                  ·
                    rfl

theorem cell21_2050361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_2050361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050361 prefixEnd_2050361 := by exact prefixLift 2050361
  have htrace : WordTrace (prefixWord ++ tailWord_2050361) baseStart_2050361 baseEnd_2050361 := by
    simpa [prefixWord, tailWord_2050361, baseEnd_2050361] using wordTrace_append hprefix tailTrace_2050361
  have hstable : (prefixWord ++ tailWord_2050361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050361).length < 2 ^ (prefixWord ++ tailWord_2050361).sum := by decide
  have hdescent : baseEnd_2050361 < baseStart_2050361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050364 : List Nat := [2, 2, 2, 2, 1, 2, 5, 2, 3]
def baseStart_2050364 : Nat := 118140960795 + 2050364 * 2 ^ 59
def prefixEnd_2050364 : Nat := 4983230072969 + 3 ^ 40 * 2050364 * 2
def baseEnd_2050364 : Nat := 467920999411253855609135

theorem tailTrace_2050364 : CollatzResearch.WordTrace tailWord_2050364 prefixEnd_2050364 467920999411253855609135 := by
  unfold tailWord_2050364
  simp only [CollatzResearch.WordTrace]
  refine ⟨37391459371944438568755073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49855279162592584758340097 37391459371944438568755073)
  ·
    refine ⟨28043594528958328926566305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37391459371944438568755073 28043594528958328926566305)
    ·
      refine ⟨21032695896718746694924729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28043594528958328926566305 21032695896718746694924729)
      ·
        refine ⟨15774521922539060021193547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21032695896718746694924729 15774521922539060021193547)
        ·
          refine ⟨23661782883808590031790321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15774521922539060021193547 23661782883808590031790321)
          ·
            refine ⟨17746337162856442523842741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23661782883808590031790321 17746337162856442523842741)
            ·
              refine ⟨1663719109017791486610257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17746337162856442523842741 1663719109017791486610257)
              ·
                refine ⟨1247789331763343614957693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663719109017791486610257 1247789331763343614957693)
                ·
                  refine ⟨467920999411253855609135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247789331763343614957693 467920999411253855609135)
                  ·
                    rfl

theorem cell21_2050364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_2050364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050364 prefixEnd_2050364 := by exact prefixLift 2050364
  have htrace : WordTrace (prefixWord ++ tailWord_2050364) baseStart_2050364 baseEnd_2050364 := by
    simpa [prefixWord, tailWord_2050364, baseEnd_2050364] using wordTrace_append hprefix tailTrace_2050364
  have hstable : (prefixWord ++ tailWord_2050364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050364).length < 2 ^ (prefixWord ++ tailWord_2050364).sum := by decide
  have hdescent : baseEnd_2050364 < baseStart_2050364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050375 : List Nat := [1, 1, 4, 1, 2, 2, 4, 6]
def baseStart_2050375 : Nat := 118140960795 + 2050375 * 2 ^ 59
def prefixEnd_2050375 : Nat := 4983230072969 + 3 ^ 40 * 2050375 * 2
def baseEnd_2050375 : Nat := 155974503253706760308593

theorem tailTrace_2050375 : CollatzResearch.WordTrace tailWord_2050375 prefixEnd_2050375 155974503253706760308593 := by
  unfold tailWord_2050375
  simp only [CollatzResearch.WordTrace]
  refine ⟨74783319946849026016160579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49855546631232684010773719 74783319946849026016160579)
  ·
    refine ⟨112174979920273539024240869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74783319946849026016160579 112174979920273539024240869)
    ·
      refine ⟨21032808735051288567045163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112174979920273539024240869 21032808735051288567045163)
      ·
        refine ⟨31549213102576932850567745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21032808735051288567045163 31549213102576932850567745)
        ·
          refine ⟨23661909826932699637925809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31549213102576932850567745 23661909826932699637925809)
          ·
            refine ⟨17746432370199524728444357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23661909826932699637925809 17746432370199524728444357)
            ·
              refine ⟨3327456069412410886583317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17746432370199524728444357 3327456069412410886583317)
              ·
                refine ⟨155974503253706760308593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3327456069412410886583317 155974503253706760308593)
                ·
                  rfl

theorem cell21_2050375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 6].length) (baseStart_2050375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050375 prefixEnd_2050375 := by exact prefixLift 2050375
  have htrace : WordTrace (prefixWord ++ tailWord_2050375) baseStart_2050375 baseEnd_2050375 := by
    simpa [prefixWord, tailWord_2050375, baseEnd_2050375] using wordTrace_append hprefix tailTrace_2050375
  have hstable : (prefixWord ++ tailWord_2050375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050375).length < 2 ^ (prefixWord ++ tailWord_2050375).sum := by decide
  have hdescent : baseEnd_2050375 < baseStart_2050375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050482 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2050482 : Nat := 118140960795 + 2050482 * 2 ^ 59
def prefixEnd_2050482 : Nat := 4983230072969 + 3 ^ 40 * 2050482 * 2
def baseEnd_2050482 : Nat := 467947928618911872642227

theorem tailTrace_2050482 : CollatzResearch.WordTrace tailWord_2050482 prefixEnd_2050482 467947928618911872642227 := by
  unfold tailWord_2050482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18696805639365345822576425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49858148371640922193537133 18696805639365345822576425)
  ·
    refine ⟨14022604229524009366932319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18696805639365345822576425 14022604229524009366932319)
    ·
      refine ⟨21033906344286014050398479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14022604229524009366932319 21033906344286014050398479)
      ·
        refine ⟨31550859516429021075597719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21033906344286014050398479 31550859516429021075597719)
        ·
          refine ⟨47326289274643531613396579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31550859516429021075597719 47326289274643531613396579)
          ·
            refine ⟨70989433911965297420094869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47326289274643531613396579 70989433911965297420094869)
            ·
              refine ⟨3327629714623373316566947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70989433911965297420094869 3327629714623373316566947)
              ·
                refine ⟨4991444571935059974850421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327629714623373316566947 4991444571935059974850421)
                ·
                  refine ⟨467947928618911872642227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4991444571935059974850421 467947928618911872642227)
                  ·
                    rfl

theorem cell21_2050482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2050482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050482 prefixEnd_2050482 := by exact prefixLift 2050482
  have htrace : WordTrace (prefixWord ++ tailWord_2050482) baseStart_2050482 baseEnd_2050482 := by
    simpa [prefixWord, tailWord_2050482, baseEnd_2050482] using wordTrace_append hprefix tailTrace_2050482
  have hstable : (prefixWord ++ tailWord_2050482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050482).length < 2 ^ (prefixWord ++ tailWord_2050482).sum := by decide
  have hdescent : baseEnd_2050482 < baseStart_2050482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050516 : List Nat := [2, 4, 1, 2, 2, 1, 3, 3, 3]
def baseStart_2050516 : Nat := 118140960795 + 2050516 * 2 ^ 59
def prefixEnd_2050516 : Nat := 4983230072969 + 3 ^ 40 * 2050516 * 2
def baseEnd_2050516 : Nat := 467955687882135369075491

theorem tailTrace_2050516 : CollatzResearch.WordTrace tailWord_2050516 prefixEnd_2050516 467955687882135369075491 := by
  unfold tailWord_2050516
  simp only [CollatzResearch.WordTrace]
  refine ⟨37394231319669103548521701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49858975092892138064695601 37394231319669103548521701)
  ·
    refine ⟨7011418372437956915347819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37394231319669103548521701 7011418372437956915347819)
    ·
      refine ⟨10517127558656935373021729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7011418372437956915347819 10517127558656935373021729)
      ·
        refine ⟨7887845668992701529766297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10517127558656935373021729 7887845668992701529766297)
        ·
          refine ⟨5915884251744526147324723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7887845668992701529766297 5915884251744526147324723)
          ·
            refine ⟨8873826377616789220987085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915884251744526147324723 8873826377616789220987085)
            ·
              refine ⟨3327684891606295957870157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8873826377616789220987085 3327684891606295957870157)
              ·
                refine ⟨1247881834352360984201309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3327684891606295957870157 1247881834352360984201309)
                ·
                  refine ⟨467955687882135369075491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247881834352360984201309 467955687882135369075491)
                  ·
                    rfl

theorem cell21_2050516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_2050516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050516 prefixEnd_2050516 := by exact prefixLift 2050516
  have htrace : WordTrace (prefixWord ++ tailWord_2050516) baseStart_2050516 baseEnd_2050516 := by
    simpa [prefixWord, tailWord_2050516, baseEnd_2050516] using wordTrace_append hprefix tailTrace_2050516
  have hstable : (prefixWord ++ tailWord_2050516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050516).length < 2 ^ (prefixWord ++ tailWord_2050516).sum := by decide
  have hdescent : baseEnd_2050516 < baseStart_2050516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050527 : List Nat := [1, 1, 2, 3, 3, 4, 7]
def baseStart_2050527 : Nat := 118140960795 + 2050527 * 2 ^ 59
def prefixEnd_2050527 : Nat := 4983230072969 + 3 ^ 40 * 2050527 * 2
def baseEnd_2050527 : Nat := 51995355359111310488015

theorem tailTrace_2050527 : CollatzResearch.WordTrace tailWord_2050527 prefixEnd_2050527 51995355359111310488015 := by
  unfold tailWord_2050527
  simp only [CollatzResearch.WordTrace]
  refine ⟨74788863842298355975693835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49859242561532237317129223 74788863842298355975693835)
  ·
    refine ⟨112183295763447533963540753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74788863842298355975693835 112183295763447533963540753)
    ·
      refine ⟨84137471822585650472655565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112183295763447533963540753 84137471822585650472655565)
      ·
        refine ⟨31551551933469618927245837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84137471822585650472655565 31551551933469618927245837)
        ·
          refine ⟨11831831975051107097717189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31551551933469618927245837 11831831975051107097717189)
          ·
            refine ⟨2218468495322082580821973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11831831975051107097717189 2218468495322082580821973)
            ·
              refine ⟨51995355359111310488015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2218468495322082580821973 51995355359111310488015)
              ·
                rfl

theorem cell21_2050527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 7].length) (baseStart_2050527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050527 prefixEnd_2050527 := by exact prefixLift 2050527
  have htrace : WordTrace (prefixWord ++ tailWord_2050527) baseStart_2050527 baseEnd_2050527 := by
    simpa [prefixWord, tailWord_2050527, baseEnd_2050527] using wordTrace_append hprefix tailTrace_2050527
  have hstable : (prefixWord ++ tailWord_2050527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050527).length < 2 ^ (prefixWord ++ tailWord_2050527).sum := by decide
  have hdescent : baseEnd_2050527 < baseStart_2050527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050533 : List Nat := [1, 3, 1, 5, 2, 1, 3, 2, 3]
def baseStart_2050533 : Nat := 118140960795 + 2050533 * 2 ^ 59
def prefixEnd_2050533 : Nat := 4983230072969 + 3 ^ 40 * 2050533 * 2
def baseEnd_2050533 : Nat := 467959567513747117292123

theorem tailTrace_2050533 : CollatzResearch.WordTrace tailWord_2050533 prefixEnd_2050533 467959567513747117292123 := by
  unfold tailWord_2050533
  simp only [CollatzResearch.WordTrace]
  refine ⟨74789082680276619000412253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49859388453517746000274835 74789082680276619000412253)
  ·
    refine ⟨28045906005103732125154595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74789082680276619000412253 28045906005103732125154595)
    ·
      refine ⟨42068859007655598187731893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28045906005103732125154595 42068859007655598187731893)
      ·
        refine ⟨3943955531967712330099865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42068859007655598187731893 3943955531967712330099865)
        ·
          refine ⟨2957966648975784247574899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3943955531967712330099865 2957966648975784247574899)
          ·
            refine ⟨4436949973463676371362349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957966648975784247574899 4436949973463676371362349)
            ·
              refine ⟨1663856240048878639260881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4436949973463676371362349 1663856240048878639260881)
              ·
                refine ⟨1247892180036658979445661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1663856240048878639260881 1247892180036658979445661)
                ·
                  refine ⟨467959567513747117292123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247892180036658979445661 467959567513747117292123)
                  ·
                    rfl

theorem cell21_2050533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_2050533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050533 prefixEnd_2050533 := by exact prefixLift 2050533
  have htrace : WordTrace (prefixWord ++ tailWord_2050533) baseStart_2050533 baseEnd_2050533 := by
    simpa [prefixWord, tailWord_2050533, baseEnd_2050533] using wordTrace_append hprefix tailTrace_2050533
  have hstable : (prefixWord ++ tailWord_2050533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050533).length < 2 ^ (prefixWord ++ tailWord_2050533).sum := by decide
  have hdescent : baseEnd_2050533 < baseStart_2050533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050589 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 4]
def baseStart_2050589 : Nat := 118140960795 + 2050589 * 2 ^ 59
def prefixEnd_2050589 : Nat := 4983230072969 + 3 ^ 40 * 2050589 * 2
def baseEnd_2050589 : Nat := 467972347476703464358675

theorem tailTrace_2050589 : CollatzResearch.WordTrace tailWord_2050589 prefixEnd_2050589 467972347476703464358675 := by
  unfold tailWord_2050589
  simp only [CollatzResearch.WordTrace]
  refine ⟨74791125168073740564450821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49860750112049160376300547 74791125168073740564450821)
  ·
    refine ⟨14023335969013826355834529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74791125168073740564450821 14023335969013826355834529)
    ·
      refine ⟨10517501976760369766875897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14023335969013826355834529 10517501976760369766875897)
      ·
        refine ⟨7888126482570277325156923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10517501976760369766875897 7888126482570277325156923)
        ·
          refine ⟨11832189723855415987735385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7888126482570277325156923 11832189723855415987735385)
          ·
            refine ⟨8874142292891561990801539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11832189723855415987735385 8874142292891561990801539)
            ·
              refine ⟨13311213439337342986202309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874142292891561990801539 13311213439337342986202309)
              ·
                refine ⟨2495852519875751809912933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13311213439337342986202309 2495852519875751809912933)
                ·
                  refine ⟨467972347476703464358675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495852519875751809912933 467972347476703464358675)
                  ·
                    rfl

theorem cell21_2050589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_2050589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050589 prefixEnd_2050589 := by exact prefixLift 2050589
  have htrace : WordTrace (prefixWord ++ tailWord_2050589) baseStart_2050589 baseEnd_2050589 := by
    simpa [prefixWord, tailWord_2050589, baseEnd_2050589] using wordTrace_append hprefix tailTrace_2050589
  have hstable : (prefixWord ++ tailWord_2050589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050589).length < 2 ^ (prefixWord ++ tailWord_2050589).sum := by decide
  have hdescent : baseEnd_2050589 < baseStart_2050589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050592 : List Nat := [2, 1, 1, 6, 2, 1, 1, 4, 3]
def baseStart_2050592 : Nat := 118140960795 + 2050592 * 2 ^ 59
def prefixEnd_2050592 : Nat := 4983230072969 + 3 ^ 40 * 2050592 * 2
def baseEnd_2050592 : Nat := 467973032117576125808669

theorem tailTrace_2050592 : CollatzResearch.WordTrace tailWord_2050592 prefixEnd_2050592 467973032117576125808669 := by
  unfold tailWord_2050592
  simp only [CollatzResearch.WordTrace]
  refine ⟨37395617293531436038405015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49860823058041914717873353 37395617293531436038405015)
  ·
    refine ⟨56093425940297154057607523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37395617293531436038405015 56093425940297154057607523)
    ·
      refine ⟨84140138910445731086411285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56093425940297154057607523 84140138910445731086411285)
      ·
        refine ⟨3944069011427143644675529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84140138910445731086411285 3944069011427143644675529)
        ·
          refine ⟨2958051758570357733506647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3944069011427143644675529 2958051758570357733506647)
          ·
            refine ⟨4437077637855536600259971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958051758570357733506647 4437077637855536600259971)
            ·
              refine ⟨6655616456783304900389957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437077637855536600259971 6655616456783304900389957)
              ·
                refine ⟨1247928085646869668823117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6655616456783304900389957 1247928085646869668823117)
                ·
                  refine ⟨467973032117576125808669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247928085646869668823117 467973032117576125808669)
                  ·
                    rfl

theorem cell21_2050592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_2050592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050592 prefixEnd_2050592 := by exact prefixLift 2050592
  have htrace : WordTrace (prefixWord ++ tailWord_2050592) baseStart_2050592 baseEnd_2050592 := by
    simpa [prefixWord, tailWord_2050592, baseEnd_2050592] using wordTrace_append hprefix tailTrace_2050592
  have hstable : (prefixWord ++ tailWord_2050592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050592).length < 2 ^ (prefixWord ++ tailWord_2050592).sum := by decide
  have hdescent : baseEnd_2050592 < baseStart_2050592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050620 : List Nat := [2, 2, 2, 2, 3, 2, 3, 5]
def baseStart_2050620 : Nat := 118140960795 + 2050620 * 2 ^ 59
def prefixEnd_2050620 : Nat := 4983230072969 + 3 ^ 40 * 2050620 * 2
def baseEnd_2050620 : Nat := 155993140699684766447315

theorem tailTrace_2050620 : CollatzResearch.WordTrace tailWord_2050620 prefixEnd_2050620 155993140699684766447315 := by
  unfold tailWord_2050620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37396127915480716429414657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49861503887307621905886209 37396127915480716429414657)
  ·
    refine ⟨28047095936610537322060993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37396127915480716429414657 28047095936610537322060993)
    ·
      refine ⟨21035321952457902991545745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28047095936610537322060993 21035321952457902991545745)
      ·
        refine ⟨15776491464343427243659309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21035321952457902991545745 15776491464343427243659309)
        ·
          refine ⟨5916184299128785216372241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15776491464343427243659309 5916184299128785216372241)
          ·
            refine ⟨4437138224346588912279181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5916184299128785216372241 4437138224346588912279181)
            ·
              refine ⟨1663926834129970842104693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4437138224346588912279181 1663926834129970842104693)
              ·
                refine ⟨155993140699684766447315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1663926834129970842104693 155993140699684766447315)
                ·
                  rfl

theorem cell21_2050620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_2050620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050620 prefixEnd_2050620 := by exact prefixLift 2050620
  have htrace : WordTrace (prefixWord ++ tailWord_2050620) baseStart_2050620 baseEnd_2050620 := by
    simpa [prefixWord, tailWord_2050620, baseEnd_2050620] using wordTrace_append hprefix tailTrace_2050620
  have hstable : (prefixWord ++ tailWord_2050620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050620).length < 2 ^ (prefixWord ++ tailWord_2050620).sum := by decide
  have hdescent : baseEnd_2050620 < baseStart_2050620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050679 : List Nat := [1, 1, 3, 1, 1, 3, 6, 5]
def baseStart_2050679 : Nat := 118140960795 + 2050679 * 2 ^ 59
def prefixEnd_2050679 : Nat := 4983230072969 + 3 ^ 40 * 2050679 * 2
def baseEnd_2050679 : Nat := 155997628900961102619497

theorem tailTrace_2050679 : CollatzResearch.WordTrace tailWord_2050679 prefixEnd_2050679 155997628900961102619497 := by
  unfold tailWord_2050679
  simp only [CollatzResearch.WordTrace]
  refine ⟨74794407737747685935227091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49862938491831790623484727 74794407737747685935227091)
  ·
    refine ⟨112191611606621528902840637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74794407737747685935227091 112191611606621528902840637)
    ·
      refine ⟨42071854352483073338565239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112191611606621528902840637 42071854352483073338565239)
      ·
        refine ⟨63107781528724610007847859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42071854352483073338565239 63107781528724610007847859)
        ·
          refine ⟨94661672293086915011771789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63107781528724610007847859 94661672293086915011771789)
          ·
            refine ⟨35498127109907593129414421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94661672293086915011771789 35498127109907593129414421)
            ·
              refine ⟨1663974708276918427941301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35498127109907593129414421 1663974708276918427941301)
              ·
                refine ⟨155997628900961102619497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1663974708276918427941301 155997628900961102619497)
                ·
                  rfl

theorem cell21_2050679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 5].length) (baseStart_2050679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050679 prefixEnd_2050679 := by exact prefixLift 2050679
  have htrace : WordTrace (prefixWord ++ tailWord_2050679) baseStart_2050679 baseEnd_2050679 := by
    simpa [prefixWord, tailWord_2050679, baseEnd_2050679] using wordTrace_append hprefix tailTrace_2050679
  have hstable : (prefixWord ++ tailWord_2050679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050679).length < 2 ^ (prefixWord ++ tailWord_2050679).sum := by decide
  have hdescent : baseEnd_2050679 < baseStart_2050679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050685 : List Nat := [1, 4, 1, 1, 6, 1, 1, 3, 3]
def baseStart_2050685 : Nat := 118140960795 + 2050685 * 2 ^ 59
def prefixEnd_2050685 : Nat := 4983230072969 + 3 ^ 40 * 2050685 * 2
def baseEnd_2050685 : Nat := 467994255984628630758479

theorem tailTrace_2050685 : CollatzResearch.WordTrace tailWord_2050685 prefixEnd_2050685 467994255984628630758479 := by
  unfold tailWord_2050685
  simp only [CollatzResearch.WordTrace]
  refine ⟨74794626575725948959945509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49863084383817299306630339 74794626575725948959945509)
  ·
    refine ⟨14023992482948615429989783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74794626575725948959945509 14023992482948615429989783)
    ·
      refine ⟨21035988724422923144984675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14023992482948615429989783 21035988724422923144984675)
      ·
        refine ⟨31553983086634384717477013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21035988724422923144984675 31553983086634384717477013)
        ·
          refine ⟨1479092957185986783631735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31553983086634384717477013 1479092957185986783631735)
          ·
            refine ⟨2218639435778980175447603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479092957185986783631735 2218639435778980175447603)
            ·
              refine ⟨3327959153668470263171405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2218639435778980175447603 3327959153668470263171405)
              ·
                refine ⟨1247984682625676348689277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3327959153668470263171405 1247984682625676348689277)
                ·
                  refine ⟨467994255984628630758479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1247984682625676348689277 467994255984628630758479)
                  ·
                    rfl

theorem cell21_2050685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_2050685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050685 prefixEnd_2050685 := by exact prefixLift 2050685
  have htrace : WordTrace (prefixWord ++ tailWord_2050685) baseStart_2050685 baseEnd_2050685 := by
    simpa [prefixWord, tailWord_2050685, baseEnd_2050685] using wordTrace_append hprefix tailTrace_2050685
  have hstable : (prefixWord ++ tailWord_2050685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050685).length < 2 ^ (prefixWord ++ tailWord_2050685).sum := by decide
  have hdescent : baseEnd_2050685 < baseStart_2050685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050769 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 5]
def baseStart_2050769 : Nat := 118140960795 + 2050769 * 2 ^ 59
def prefixEnd_2050769 : Nat := 4983230072969 + 3 ^ 40 * 2050769 * 2
def baseEnd_2050769 : Nat := 468013425929063151358307

theorem tailTrace_2050769 : CollatzResearch.WordTrace tailWord_2050769 prefixEnd_2050769 468013425929063151358307 := by
  unfold tailWord_2050769
  simp only [CollatzResearch.WordTrace]
  refine ⟨74797690307421631306003361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49865126871614420870668907 74797690307421631306003361)
  ·
    refine ⟨56098267730566223479502521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74797690307421631306003361 56098267730566223479502521)
    ·
      refine ⟨42073700797924667609626891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56098267730566223479502521 42073700797924667609626891)
      ·
        refine ⟨63110551196887001414440337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42073700797924667609626891 63110551196887001414440337)
        ·
          refine ⟨47332913397665251060830253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63110551196887001414440337 47332913397665251060830253)
          ·
            refine ⟨17749842524124469147811345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47332913397665251060830253 17749842524124469147811345)
            ·
              refine ⟨13312381893093351860858509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17749842524124469147811345 13312381893093351860858509)
              ·
                refine ⟨4992143209910006947821941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13312381893093351860858509 4992143209910006947821941)
                ·
                  refine ⟨468013425929063151358307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4992143209910006947821941 468013425929063151358307)
                  ·
                    rfl

theorem cell21_2050769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_2050769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050769 prefixEnd_2050769 := by exact prefixLift 2050769
  have htrace : WordTrace (prefixWord ++ tailWord_2050769) baseStart_2050769 baseEnd_2050769 := by
    simpa [prefixWord, tailWord_2050769, baseEnd_2050769] using wordTrace_append hprefix tailTrace_2050769
  have hstable : (prefixWord ++ tailWord_2050769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050769).length < 2 ^ (prefixWord ++ tailWord_2050769).sum := by decide
  have hdescent : baseEnd_2050769 < baseStart_2050769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050848 : List Nat := [2, 1, 1, 5, 1, 4, 2, 5]
def baseStart_2050848 : Nat := 118140960795 + 2050848 * 2 ^ 59
def prefixEnd_2050848 : Nat := 4983230072969 + 3 ^ 40 * 2050848 * 2
def baseEnd_2050848 : Nat := 156010484935125523180493

theorem tailTrace_2050848 : CollatzResearch.WordTrace tailWord_2050848 prefixEnd_2050848 156010484935125523180493 := by
  unfold tailWord_2050848
  simp only [CollatzResearch.WordTrace]
  refine ⟨37400285837067713899064599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49867047782756951865419465 37400285837067713899064599)
  ·
    refine ⟨56100428755601570848596899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37400285837067713899064599 56100428755601570848596899)
    ·
      refine ⟨84150643133402356272895349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56100428755601570848596899 84150643133402356272895349)
      ·
        refine ⟨7889122793756470900583939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84150643133402356272895349 7889122793756470900583939)
        ·
          refine ⟨11833684190634706350875909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7889122793756470900583939 11833684190634706350875909)
          ·
            refine ⟨2218815785744007440789233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11833684190634706350875909 2218815785744007440789233)
            ·
              refine ⟨1664111839308005580591925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2218815785744007440789233 1664111839308005580591925)
              ·
                refine ⟨156010484935125523180493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1664111839308005580591925 156010484935125523180493)
                ·
                  rfl

theorem cell21_2050848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_2050848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050848 prefixEnd_2050848 := by exact prefixLift 2050848
  have htrace : WordTrace (prefixWord ++ tailWord_2050848) baseStart_2050848 baseEnd_2050848 := by
    simpa [prefixWord, tailWord_2050848, baseEnd_2050848] using wordTrace_append hprefix tailTrace_2050848
  have hstable : (prefixWord ++ tailWord_2050848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050848).length < 2 ^ (prefixWord ++ tailWord_2050848).sum := by decide
  have hdescent : baseEnd_2050848 < baseStart_2050848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050859 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 6]
def baseStart_2050859 : Nat := 118140960795 + 2050859 * 2 ^ 59
def prefixEnd_2050859 : Nat := 4983230072969 + 3 ^ 40 * 2050859 * 2
def baseEnd_2050859 : Nat := 468033965155242994858123

theorem tailTrace_2050859 : CollatzResearch.WordTrace tailWord_2050859 prefixEnd_2050859 468033965155242994858123 := by
  unfold tailWord_2050859
  simp only [CollatzResearch.WordTrace]
  refine ⟨74800972877095576676779631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49867315251397051117853087 74800972877095576676779631)
  ·
    refine ⟨112201459315643365015169447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74800972877095576676779631 112201459315643365015169447)
    ·
      refine ⟨168302188973465047522754171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112201459315643365015169447 168302188973465047522754171)
      ·
        refine ⟨252453283460197571284131257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168302188973465047522754171 252453283460197571284131257)
        ·
          refine ⟨189339962595148178463098443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252453283460197571284131257 189339962595148178463098443)
          ·
            refine ⟨284009943892722267694647665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189339962595148178463098443 284009943892722267694647665)
            ·
              refine ⟨213007457919541700770985749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284009943892722267694647665 213007457919541700770985749)
              ·
                refine ⟨9984724589978517223639957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 213007457919541700770985749 9984724589978517223639957)
                ·
                  refine ⟨468033965155242994858123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9984724589978517223639957 468033965155242994858123)
                  ·
                    rfl

theorem cell21_2050859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_2050859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050859 prefixEnd_2050859 := by exact prefixLift 2050859
  have htrace : WordTrace (prefixWord ++ tailWord_2050859) baseStart_2050859 baseEnd_2050859 := by
    simpa [prefixWord, tailWord_2050859, baseEnd_2050859] using wordTrace_append hprefix tailTrace_2050859
  have hstable : (prefixWord ++ tailWord_2050859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050859).length < 2 ^ (prefixWord ++ tailWord_2050859).sum := by decide
  have hdescent : baseEnd_2050859 < baseStart_2050859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050876 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_2050876 : Nat := 118140960795 + 2050876 * 2 ^ 59
def prefixEnd_2050876 : Nat := 4983230072969 + 3 ^ 40 * 2050876 * 2
def baseEnd_2050876 : Nat := 468037844786854743074755

theorem tailTrace_2050876 : CollatzResearch.WordTrace tailWord_2050876 prefixEnd_2050876 468037844786854743074755 := by
  unfold tailWord_2050876
  simp only [CollatzResearch.WordTrace]
  refine ⟨37400796459016994290074241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49867728612022659053432321 37400796459016994290074241)
  ·
    refine ⟨28050597344262745717555681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37400796459016994290074241 28050597344262745717555681)
    ·
      refine ⟨21037948008197059288166761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28050597344262745717555681 21037948008197059288166761)
      ·
        refine ⟨15778461006147794466125071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21037948008197059288166761 15778461006147794466125071)
        ·
          refine ⟨23667691509221691699187607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15778461006147794466125071 23667691509221691699187607)
          ·
            refine ⟨35501537263832537548781411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23667691509221691699187607 35501537263832537548781411)
            ·
              refine ⟨53252305895748806323172117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35501537263832537548781411 53252305895748806323172117)
              ·
                refine ⟨2496201838863225296398693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53252305895748806323172117 2496201838863225296398693)
                ·
                  refine ⟨468037844786854743074755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2496201838863225296398693 468037844786854743074755)
                  ·
                    rfl

theorem cell21_2050876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_2050876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050876 prefixEnd_2050876 := by exact prefixLift 2050876
  have htrace : WordTrace (prefixWord ++ tailWord_2050876) baseStart_2050876 baseEnd_2050876 := by
    simpa [prefixWord, tailWord_2050876, baseEnd_2050876] using wordTrace_append hprefix tailTrace_2050876
  have hstable : (prefixWord ++ tailWord_2050876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050876).length < 2 ^ (prefixWord ++ tailWord_2050876).sum := by decide
  have hdescent : baseEnd_2050876 < baseStart_2050876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050935 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 6]
def baseStart_2050935 : Nat := 118140960795 + 2050935 * 2 ^ 59
def prefixEnd_2050935 : Nat := 4983230072969 + 3 ^ 40 * 2050935 * 2
def baseEnd_2050935 : Nat := 468051309390683751591301

theorem tailTrace_2050935 : CollatzResearch.WordTrace tailWord_2050935 prefixEnd_2050935 468051309390683751591301 := by
  unfold tailWord_2050935
  simp only [CollatzResearch.WordTrace]
  refine ⟨74803744824820241656546259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49869163216546827771030839 74803744824820241656546259)
  ·
    refine ⟨112205617237230362484819389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74803744824820241656546259 112205617237230362484819389)
    ·
      refine ⟨42077106463961385931807271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112205617237230362484819389 42077106463961385931807271)
      ·
        refine ⟨63115659695942078897710907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42077106463961385931807271 63115659695942078897710907)
        ·
          refine ⟨94673489543913118346566361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63115659695942078897710907 94673489543913118346566361)
          ·
            refine ⟨71005117157934838759924771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94673489543913118346566361 71005117157934838759924771)
            ·
              refine ⟨106507675736902258139887157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71005117157934838759924771 106507675736902258139887157)
              ·
                refine ⟨9985094600334586700614421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106507675736902258139887157 9985094600334586700614421)
                ·
                  refine ⟨468051309390683751591301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9985094600334586700614421 468051309390683751591301)
                  ·
                    rfl

theorem cell21_2050935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_2050935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050935 prefixEnd_2050935 := by exact prefixLift 2050935
  have htrace : WordTrace (prefixWord ++ tailWord_2050935) baseStart_2050935 baseEnd_2050935 := by
    simpa [prefixWord, tailWord_2050935, baseEnd_2050935] using wordTrace_append hprefix tailTrace_2050935
  have hstable : (prefixWord ++ tailWord_2050935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050935).length < 2 ^ (prefixWord ++ tailWord_2050935).sum := by decide
  have hdescent : baseEnd_2050935 < baseStart_2050935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050972 : List Nat := [2, 2, 3, 3, 2, 1, 2, 3, 3]
def baseStart_2050972 : Nat := 118140960795 + 2050972 * 2 ^ 59
def prefixEnd_2050972 : Nat := 4983230072969 + 3 ^ 40 * 2050972 * 2
def baseEnd_2050972 : Nat := 468059753294779909474559

theorem tailTrace_2050972 : CollatzResearch.WordTrace tailWord_2050972 prefixEnd_2050972 468059753294779909474559 := by
  unfold tailWord_2050972
  simp only [CollatzResearch.WordTrace]
  refine ⟨37402547162843098487821585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49870062883790797983762113 37402547162843098487821585)
  ·
    refine ⟨28051910372132323865866189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37402547162843098487821585 28051910372132323865866189)
    ·
      refine ⟨10519466389549621449699821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28051910372132323865866189 10519466389549621449699821)
      ·
        refine ⟨3944799896081108043637433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10519466389549621449699821 3944799896081108043637433)
        ·
          refine ⟨2958599922060831032728075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3944799896081108043637433 2958599922060831032728075)
          ·
            refine ⟨4437899883091246549092113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958599922060831032728075 4437899883091246549092113)
            ·
              refine ⟨3328424912318434911819085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4437899883091246549092113 3328424912318434911819085)
              ·
                refine ⟨1248159342119413091932157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3328424912318434911819085 1248159342119413091932157)
                ·
                  refine ⟨468059753294779909474559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248159342119413091932157 468059753294779909474559)
                  ·
                    rfl

theorem cell21_2050972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_2050972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050972 prefixEnd_2050972 := by exact prefixLift 2050972
  have htrace : WordTrace (prefixWord ++ tailWord_2050972) baseStart_2050972 baseEnd_2050972 := by
    simpa [prefixWord, tailWord_2050972, baseEnd_2050972] using wordTrace_append hprefix tailTrace_2050972
  have hstable : (prefixWord ++ tailWord_2050972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050972).length < 2 ^ (prefixWord ++ tailWord_2050972).sum := by decide
  have hdescent : baseEnd_2050972 < baseStart_2050972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2050983 : List Nat := [1, 1, 6, 1, 3, 1, 8]
def baseStart_2050983 : Nat := 118140960795 + 2050983 * 2 ^ 59
def prefixEnd_2050983 : Nat := 4983230072969 + 3 ^ 40 * 2050983 * 2
def baseEnd_2050983 : Nat := 52006918182738481643467

theorem tailTrace_2050983 : CollatzResearch.WordTrace tailWord_2050983 prefixEnd_2050983 52006918182738481643467 := by
  unfold tailWord_2050983
  simp only [CollatzResearch.WordTrace]
  refine ⟨74805495528646345854293603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49870330352430897236195735 74805495528646345854293603)
  ·
    refine ⟨112208243292969518781440405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74805495528646345854293603 112208243292969518781440405)
    ·
      refine ⟨5259761404357946192880019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112208243292969518781440405 5259761404357946192880019)
      ·
        refine ⟨7889642106536919289320029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5259761404357946192880019 7889642106536919289320029)
        ·
          refine ⟨2958615789951344733495011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7889642106536919289320029 2958615789951344733495011)
          ·
            refine ⟨4437923684927017100242517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958615789951344733495011 4437923684927017100242517)
            ·
              refine ⟨52006918182738481643467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4437923684927017100242517 52006918182738481643467)
              ·
                rfl

theorem cell21_2050983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 8].length) (baseStart_2050983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2050983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2050983 prefixEnd_2050983 := by exact prefixLift 2050983
  have htrace : WordTrace (prefixWord ++ tailWord_2050983) baseStart_2050983 baseEnd_2050983 := by
    simpa [prefixWord, tailWord_2050983, baseEnd_2050983] using wordTrace_append hprefix tailTrace_2050983
  have hstable : (prefixWord ++ tailWord_2050983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2050983).length < 2 ^ (prefixWord ++ tailWord_2050983).sum := by decide
  have hdescent : baseEnd_2050983 < baseStart_2050983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2050983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051028 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2051028 : Nat := 118140960795 + 2051028 * 2 ^ 59
def prefixEnd_2051028 : Nat := 4983230072969 + 3 ^ 40 * 2051028 * 2
def baseEnd_2051028 : Nat := 468072533257736256541111

theorem tailTrace_2051028 : CollatzResearch.WordTrace tailWord_2051028 prefixEnd_2051028 468072533257736256541111 := by
  unfold tailWord_2051028
  simp only [CollatzResearch.WordTrace]
  refine ⟨37403568406741659269840869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49871424542322212359787825 37403568406741659269840869)
  ·
    refine ⟨7013169076264061113095163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37403568406741659269840869 7013169076264061113095163)
    ·
      refine ⟨10519753614396091669642745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7013169076264061113095163 10519753614396091669642745)
      ·
        refine ⟨7889815210797068752232059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10519753614396091669642745 7889815210797068752232059)
        ·
          refine ⟨11834722816195603128348089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7889815210797068752232059 11834722816195603128348089)
          ·
            refine ⟨8876042112146702346261067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11834722816195603128348089 8876042112146702346261067)
            ·
              refine ⟨13314063168220053519391601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876042112146702346261067 13314063168220053519391601)
              ·
                refine ⟨9985547376165040139543701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13314063168220053519391601 9985547376165040139543701)
                ·
                  refine ⟨468072533257736256541111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9985547376165040139543701 468072533257736256541111)
                  ·
                    rfl

theorem cell21_2051028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2051028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051028 prefixEnd_2051028 := by exact prefixLift 2051028
  have htrace : WordTrace (prefixWord ++ tailWord_2051028) baseStart_2051028 baseEnd_2051028 := by
    simpa [prefixWord, tailWord_2051028, baseEnd_2051028] using wordTrace_append hprefix tailTrace_2051028
  have hstable : (prefixWord ++ tailWord_2051028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051028).length < 2 ^ (prefixWord ++ tailWord_2051028).sum := by decide
  have hdescent : baseEnd_2051028 < baseStart_2051028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051062 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2051062 : Nat := 118140960795 + 2051062 * 2 ^ 59
def prefixEnd_2051062 : Nat := 4983230072969 + 3 ^ 40 * 2051062 * 2
def baseEnd_2051062 : Nat := 468080292520959752974375

theorem tailTrace_2051062 : CollatzResearch.WordTrace tailWord_2051062 prefixEnd_2051062 468080292520959752974375 := by
  unfold tailWord_2051062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4675523555960008896651215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49872251263573428230946293 4675523555960008896651215)
  ·
    refine ⟨7013285333940013344976823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4675523555960008896651215 7013285333940013344976823)
    ·
      refine ⟨10519928000910020017465235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7013285333940013344976823 10519928000910020017465235)
      ·
        refine ⟨15779892001365030026197853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519928000910020017465235 15779892001365030026197853)
        ·
          refine ⟨5917459500511886259824195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15779892001365030026197853 5917459500511886259824195)
          ·
            refine ⟨8876189250767829389736293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917459500511886259824195 8876189250767829389736293)
            ·
              refine ⟨1664285484518968010575555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8876189250767829389736293 1664285484518968010575555)
              ·
                refine ⟨2496428226778452015863333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664285484518968010575555 2496428226778452015863333)
                ·
                  refine ⟨468080292520959752974375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2496428226778452015863333 468080292520959752974375)
                  ·
                    rfl

theorem cell21_2051062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2051062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051062 prefixEnd_2051062 := by exact prefixLift 2051062
  have htrace : WordTrace (prefixWord ++ tailWord_2051062) baseStart_2051062 baseEnd_2051062 := by
    simpa [prefixWord, tailWord_2051062, baseEnd_2051062] using wordTrace_append hprefix tailTrace_2051062
  have hstable : (prefixWord ++ tailWord_2051062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051062).length < 2 ^ (prefixWord ++ tailWord_2051062).sum := by decide
  have hdescent : baseEnd_2051062 < baseStart_2051062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051107 : List Nat := [1, 1, 1, 4, 3, 2, 4, 2, 3]
def baseStart_2051107 : Nat := 118140960795 + 2051107 * 2 ^ 59
def prefixEnd_2051107 : Nat := 4983230072969 + 3 ^ 40 * 2051107 * 2
def baseEnd_2051107 : Nat := 468090562134049674724283

theorem tailTrace_2051107 : CollatzResearch.WordTrace tailWord_2051107 prefixEnd_2051107 468090562134049674724283 := by
  unfold tailWord_2051107
  simp only [CollatzResearch.WordTrace]
  refine ⟨74810018180197115031807575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49873345453464743354538383 74810018180197115031807575)
  ·
    refine ⟨112215027270295672547711363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74810018180197115031807575 112215027270295672547711363)
    ·
      refine ⟨168322540905443508821567045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112215027270295672547711363 168322540905443508821567045)
      ·
        refine ⟨31560476419770657904043821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168322540905443508821567045 31560476419770657904043821)
        ·
          refine ⟨11835178657413996714016433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31560476419770657904043821 11835178657413996714016433)
          ·
            refine ⟨8876383993060497535512325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11835178657413996714016433 8876383993060497535512325)
            ·
              refine ⟨1664321998698843287908561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8876383993060497535512325 1664321998698843287908561)
              ·
                refine ⟨1248241499024132465931421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664321998698843287908561 1248241499024132465931421)
                ·
                  refine ⟨468090562134049674724283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248241499024132465931421 468090562134049674724283)
                  ·
                    rfl

theorem cell21_2051107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 3].length) (baseStart_2051107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051107 prefixEnd_2051107 := by exact prefixLift 2051107
  have htrace : WordTrace (prefixWord ++ tailWord_2051107) baseStart_2051107 baseEnd_2051107 := by
    simpa [prefixWord, tailWord_2051107, baseEnd_2051107] using wordTrace_append hprefix tailTrace_2051107
  have hstable : (prefixWord ++ tailWord_2051107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051107).length < 2 ^ (prefixWord ++ tailWord_2051107).sum := by decide
  have hdescent : baseEnd_2051107 < baseStart_2051107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051231 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 4]
def baseStart_2051231 : Nat := 118140960795 + 2051231 * 2 ^ 59
def prefixEnd_2051231 : Nat := 4983230072969 + 3 ^ 40 * 2051231 * 2
def baseEnd_2051231 : Nat := 468118860623453014657363

theorem tailTrace_2051231 : CollatzResearch.WordTrace tailWord_2051231 prefixEnd_2051231 468118860623453014657363 := by
  unfold tailWord_2051231
  simp only [CollatzResearch.WordTrace]
  refine ⟨74814540831747884209321547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49876360554498589472881031 74814540831747884209321547)
  ·
    refine ⟨112221811247621826313982321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74814540831747884209321547 112221811247621826313982321)
    ·
      refine ⟨84166358435716369735486741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112221811247621826313982321 84166358435716369735486741)
      ·
        refine ⟨3945298051674204831350941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84166358435716369735486741 3945298051674204831350941)
        ·
          refine ⟨1479486769377826811756603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3945298051674204831350941 1479486769377826811756603)
          ·
            refine ⟨2219230154066740217634905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479486769377826811756603 2219230154066740217634905)
            ·
              refine ⟨1664422615550055163226179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219230154066740217634905 1664422615550055163226179)
              ·
                refine ⟨2496633923325082744839269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1664422615550055163226179 2496633923325082744839269)
                ·
                  refine ⟨468118860623453014657363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2496633923325082744839269 468118860623453014657363)
                  ·
                    rfl

theorem cell21_2051231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 4].length) (baseStart_2051231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051231 prefixEnd_2051231 := by exact prefixLift 2051231
  have htrace : WordTrace (prefixWord ++ tailWord_2051231) baseStart_2051231 baseEnd_2051231 := by
    simpa [prefixWord, tailWord_2051231, baseEnd_2051231] using wordTrace_append hprefix tailTrace_2051231
  have hstable : (prefixWord ++ tailWord_2051231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051231).length < 2 ^ (prefixWord ++ tailWord_2051231).sum := by decide
  have hdescent : baseEnd_2051231 < baseStart_2051231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051332 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_2051332 : Nat := 118140960795 + 2051332 * 2 ^ 59
def prefixEnd_2051332 : Nat := 4983230072969 + 3 ^ 40 * 2051332 * 2
def baseEnd_2051332 : Nat := 468141910199499283473823

theorem tailTrace_2051332 : CollatzResearch.WordTrace tailWord_2051332 prefixEnd_2051332 468141910199499283473823 := by
  unfold tailWord_2051332
  simp only [CollatzResearch.WordTrace]
  refine ⟨37409112302190989229374125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49878816402921318972498833 37409112302190989229374125)
  ·
    refine ⟨14028417113321620961015297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37409112302190989229374125 14028417113321620961015297)
    ·
      refine ⟨10521312834991215720761473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14028417113321620961015297 10521312834991215720761473)
      ·
        refine ⟨7890984626243411790571105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10521312834991215720761473 7890984626243411790571105)
        ·
          refine ⟨5918238469682558842928329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7890984626243411790571105 5918238469682558842928329)
          ·
            refine ⟨4438678852261919132196247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5918238469682558842928329 4438678852261919132196247)
            ·
              refine ⟨6658018278392878698294371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438678852261919132196247 6658018278392878698294371)
              ·
                refine ⟨9987027417589318047441557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6658018278392878698294371 9987027417589318047441557)
                ·
                  refine ⟨468141910199499283473823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9987027417589318047441557 468141910199499283473823)
                  ·
                    rfl

theorem cell21_2051332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_2051332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051332 prefixEnd_2051332 := by exact prefixLift 2051332
  have htrace : WordTrace (prefixWord ++ tailWord_2051332) baseStart_2051332 baseEnd_2051332 := by
    simpa [prefixWord, tailWord_2051332, baseEnd_2051332] using wordTrace_append hprefix tailTrace_2051332
  have hstable : (prefixWord ++ tailWord_2051332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051332).length < 2 ^ (prefixWord ++ tailWord_2051332).sum := by decide
  have hdescent : baseEnd_2051332 < baseStart_2051332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051363 : List Nat := [1, 1, 1, 4, 2, 5, 2, 5]
def baseStart_2051363 : Nat := 118140960795 + 2051363 * 2 ^ 59
def prefixEnd_2051363 : Nat := 4983230072969 + 3 ^ 40 * 2051363 * 2
def baseEnd_2051363 : Nat := 156049661607283372819031

theorem tailTrace_2051363 : CollatzResearch.WordTrace tailWord_2051363 prefixEnd_2051363 156049661607283372819031 := by
  unfold tailWord_2051363
  simp only [CollatzResearch.WordTrace]
  refine ⟨74819355267269670753126743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49879570178179780502084495 74819355267269670753126743)
  ·
    refine ⟨112229032900904506129690115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74819355267269670753126743 112229032900904506129690115)
    ·
      refine ⟨168343549351356759194535173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112229032900904506129690115 168343549351356759194535173)
      ·
        refine ⟨31564415503379392348975345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168343549351356759194535173 31564415503379392348975345)
        ·
          refine ⟨23673311627534544261731509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31564415503379392348975345 23673311627534544261731509)
          ·
            refine ⟨2219372965081363524537329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23673311627534544261731509 2219372965081363524537329)
            ·
              refine ⟨1664529723811022643402997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219372965081363524537329 1664529723811022643402997)
              ·
                refine ⟨156049661607283372819031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1664529723811022643402997 156049661607283372819031)
                ·
                  rfl

theorem cell21_2051363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 5].length) (baseStart_2051363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051363 prefixEnd_2051363 := by exact prefixLift 2051363
  have htrace : WordTrace (prefixWord ++ tailWord_2051363) baseStart_2051363 baseEnd_2051363 := by
    simpa [prefixWord, tailWord_2051363, baseEnd_2051363] using wordTrace_append hprefix tailTrace_2051363
  have hstable : (prefixWord ++ tailWord_2051363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051363).length < 2 ^ (prefixWord ++ tailWord_2051363).sum := by decide
  have hdescent : baseEnd_2051363 < baseStart_2051363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051391 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 6]
def baseStart_2051391 : Nat := 118140960795 + 2051391 * 2 ^ 59
def prefixEnd_2051391 : Nat := 4983230072969 + 3 ^ 40 * 2051391 * 2
def baseEnd_2051391 : Nat := 468155374803328291990369

theorem tailTrace_2051391 : CollatzResearch.WordTrace tailWord_2051391 prefixEnd_2051391 468155374803328291990369 := by
  unfold tailWord_2051391
  simp only [CollatzResearch.WordTrace]
  refine ⟨74820376511168231535146027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49880251007445487690097351 74820376511168231535146027)
  ·
    refine ⟨112230564766752347302719041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74820376511168231535146027 112230564766752347302719041)
    ·
      refine ⟨84172923575064260477039281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112230564766752347302719041 84172923575064260477039281)
      ·
        refine ⟨63129692681298195357779461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84172923575064260477039281 63129692681298195357779461)
        ·
          refine ⟨11836817377743411629583649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63129692681298195357779461 11836817377743411629583649)
          ·
            refine ⟨8877613033307558722187737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11836817377743411629583649 8877613033307558722187737)
            ·
              refine ⟨6658209774980669041640803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8877613033307558722187737 6658209774980669041640803)
              ·
                refine ⟨9987314662471003562461205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6658209774980669041640803 9987314662471003562461205)
                ·
                  refine ⟨468155374803328291990369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9987314662471003562461205 468155374803328291990369)
                  ·
                    rfl

theorem cell21_2051391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_2051391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051391 prefixEnd_2051391 := by exact prefixLift 2051391
  have htrace : WordTrace (prefixWord ++ tailWord_2051391) baseStart_2051391 baseEnd_2051391 := by
    simpa [prefixWord, tailWord_2051391, baseEnd_2051391] using wordTrace_append hprefix tailTrace_2051391
  have hstable : (prefixWord ++ tailWord_2051391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051391).length < 2 ^ (prefixWord ++ tailWord_2051391).sum := by decide
  have hdescent : baseEnd_2051391 < baseStart_2051391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051445 : List Nat := [1, 3, 4, 1, 4, 1, 2, 2, 3]
def baseStart_2051445 : Nat := 118140960795 + 2051445 * 2 ^ 59
def prefixEnd_2051445 : Nat := 4983230072969 + 3 ^ 40 * 2051445 * 2
def baseEnd_2051445 : Nat := 468167698339036198090259

theorem tailTrace_2051445 : CollatzResearch.WordTrace tailWord_2051445 prefixEnd_2051445 468167698339036198090259 := by
  unfold tailWord_2051445
  simp only [CollatzResearch.WordTrace]
  refine ⟨74822346052972598757611789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49881564035315065838407859 74822346052972598757611789)
  ·
    refine ⟨28058379769864724534104421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74822346052972598757611789 28058379769864724534104421)
    ·
      refine ⟨5260946206849635850144579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28058379769864724534104421 5260946206849635850144579)
      ·
        refine ⟨7891419310274453775216869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5260946206849635850144579 7891419310274453775216869)
        ·
          refine ⟨1479641120676460082853163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7891419310274453775216869 1479641120676460082853163)
          ·
            refine ⟨2219461681014690124279745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479641120676460082853163 2219461681014690124279745)
            ·
              refine ⟨1664596260761017593209809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219461681014690124279745 1664596260761017593209809)
              ·
                refine ⟨1248447195570763194907357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664596260761017593209809 1248447195570763194907357)
                ·
                  refine ⟨468167698339036198090259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248447195570763194907357 468167698339036198090259)
                  ·
                    rfl

theorem cell21_2051445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_2051445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051445 prefixEnd_2051445 := by exact prefixLift 2051445
  have htrace : WordTrace (prefixWord ++ tailWord_2051445) baseStart_2051445 baseEnd_2051445 := by
    simpa [prefixWord, tailWord_2051445, baseEnd_2051445] using wordTrace_append hprefix tailTrace_2051445
  have hstable : (prefixWord ++ tailWord_2051445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051445).length < 2 ^ (prefixWord ++ tailWord_2051445).sum := by decide
  have hdescent : baseEnd_2051445 < baseStart_2051445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051467 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 4]
def baseStart_2051467 : Nat := 118140960795 + 2051467 * 2 ^ 59
def prefixEnd_2051467 : Nat := 4983230072969 + 3 ^ 40 * 2051467 * 2
def baseEnd_2051467 : Nat := 468172719038769048723547

theorem tailTrace_2051467 : CollatzResearch.WordTrace tailWord_2051467 prefixEnd_2051467 468172719038769048723547 := by
  unfold tailWord_2051467
  simp only [CollatzResearch.WordTrace]
  refine ⟨74823148458892896514912655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49882098972595264343275103 74823148458892896514912655)
  ·
    refine ⟨112234722688339344772368983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74823148458892896514912655 112234722688339344772368983)
    ·
      refine ⟨168352084032509017158553475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112234722688339344772368983 168352084032509017158553475)
      ·
        refine ⟨252528126048763525737830213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168352084032509017158553475 252528126048763525737830213)
        ·
          refine ⟨47349023634143161075843165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252528126048763525737830213 47349023634143161075843165)
          ·
            refine ⟨17755883862803685403441187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47349023634143161075843165 17755883862803685403441187)
            ·
              refine ⟨26633825794205528105161781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17755883862803685403441187 26633825794205528105161781)
              ·
                refine ⟨2496921168206768259858917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26633825794205528105161781 2496921168206768259858917)
                ·
                  refine ⟨468172719038769048723547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2496921168206768259858917 468172719038769048723547)
                  ·
                    rfl

theorem cell21_2051467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 4].length) (baseStart_2051467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051467 prefixEnd_2051467 := by exact prefixLift 2051467
  have htrace : WordTrace (prefixWord ++ tailWord_2051467) baseStart_2051467 baseEnd_2051467 := by
    simpa [prefixWord, tailWord_2051467, baseEnd_2051467] using wordTrace_append hprefix tailTrace_2051467
  have hstable : (prefixWord ++ tailWord_2051467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051467).length < 2 ^ (prefixWord ++ tailWord_2051467).sum := by decide
  have hdescent : baseEnd_2051467 < baseStart_2051467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051470 : List Nat := [4, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_2051470 : Nat := 118140960795 + 2051470 * 2 ^ 59
def prefixEnd_2051470 : Nat := 4983230072969 + 3 ^ 40 * 2051470 * 2
def baseEnd_2051470 : Nat := 468173403679641710173541

theorem tailTrace_2051470 : CollatzResearch.WordTrace tailWord_2051470 prefixEnd_2051470 468173403679641710173541 := by
  unfold tailWord_2051470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9352907234735253503408983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49882171918588018684847909 9352907234735253503408983)
  ·
    refine ⟨14029360852102880255113475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9352907234735253503408983 14029360852102880255113475)
    ·
      refine ⟨21044041278154320382670213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14029360852102880255113475 21044041278154320382670213)
      ·
        refine ⟨3945757739653935071750665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21044041278154320382670213 3945757739653935071750665)
        ·
          refine ⟨2959318304740451303812999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3945757739653935071750665 2959318304740451303812999)
          ·
            refine ⟨4438977457110676955719499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959318304740451303812999 4438977457110676955719499)
            ·
              refine ⟨6658466185666015433579249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438977457110676955719499 6658466185666015433579249)
              ·
                refine ⟨4993849639249511575184437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658466185666015433579249 4993849639249511575184437)
                ·
                  refine ⟨468173403679641710173541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4993849639249511575184437 468173403679641710173541)
                  ·
                    rfl

theorem cell21_2051470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_2051470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051470 prefixEnd_2051470 := by exact prefixLift 2051470
  have htrace : WordTrace (prefixWord ++ tailWord_2051470) baseStart_2051470 baseEnd_2051470 := by
    simpa [prefixWord, tailWord_2051470, baseEnd_2051470] using wordTrace_append hprefix tailTrace_2051470
  have hstable : (prefixWord ++ tailWord_2051470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051470).length < 2 ^ (prefixWord ++ tailWord_2051470).sum := by decide
  have hdescent : baseEnd_2051470 < baseStart_2051470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051501 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2051501 : Nat := 118140960795 + 2051501 * 2 ^ 59
def prefixEnd_2051501 : Nat := 4983230072969 + 3 ^ 40 * 2051501 * 2
def baseEnd_2051501 : Nat := 468180478301992545156811

theorem tailTrace_2051501 : CollatzResearch.WordTrace tailWord_2051501 prefixEnd_2051501 468180478301992545156811 := by
  unfold tailWord_2051501
  simp only [CollatzResearch.WordTrace]
  refine ⟨74824388540769720321650357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49882925693846480214433571 74824388540769720321650357)
  ·
    refine ⟨7014786425697161280154721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74824388540769720321650357 7014786425697161280154721)
    ·
      refine ⟨5261089819272870960116041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7014786425697161280154721 5261089819272870960116041)
      ·
        refine ⟨3945817364454653220087031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5261089819272870960116041 3945817364454653220087031)
        ·
          refine ⟨5918726046681979830130547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3945817364454653220087031 5918726046681979830130547)
          ·
            refine ⟨8878089070022969745195821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918726046681979830130547 8878089070022969745195821)
            ·
              refine ⟨3329283401258613654448433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8878089070022969745195821 3329283401258613654448433)
              ·
                refine ⟨2496962550943960240836325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3329283401258613654448433 2496962550943960240836325)
                ·
                  refine ⟨468180478301992545156811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2496962550943960240836325 468180478301992545156811)
                  ·
                    rfl

theorem cell21_2051501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2051501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051501 prefixEnd_2051501 := by exact prefixLift 2051501
  have htrace : WordTrace (prefixWord ++ tailWord_2051501) baseStart_2051501 baseEnd_2051501 := by
    simpa [prefixWord, tailWord_2051501, baseEnd_2051501] using wordTrace_append hprefix tailTrace_2051501
  have hstable : (prefixWord ++ tailWord_2051501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051501).length < 2 ^ (prefixWord ++ tailWord_2051501).sum := by decide
  have hdescent : baseEnd_2051501 < baseStart_2051501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051512 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_2051512 : Nat := 118140960795 + 2051512 * 2 ^ 59
def prefixEnd_2051512 : Nat := 4983230072969 + 3 ^ 40 * 2051512 * 2
def baseEnd_2051512 : Nat := 468182988651858970473455

theorem tailTrace_2051512 : CollatzResearch.WordTrace tailWord_2051512 prefixEnd_2051512 468182988651858970473455 := by
  unfold tailWord_2051512
  simp only [CollatzResearch.WordTrace]
  refine ⟨37412394871864934600150395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49883193162486579466867193 37412394871864934600150395)
  ·
    refine ⟨56118592307797401900225593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37412394871864934600150395 56118592307797401900225593)
    ·
      refine ⟨42088944230848051425169195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56118592307797401900225593 42088944230848051425169195)
      ·
        refine ⟨63133416346272077137753793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42088944230848051425169195 63133416346272077137753793)
        ·
          refine ⟨47350062259704057853315345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63133416346272077137753793 47350062259704057853315345)
          ·
            refine ⟨35512546694778043389986509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47350062259704057853315345 35512546694778043389986509)
            ·
              refine ⟨13317205010541766271244941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35512546694778043389986509 13317205010541766271244941)
              ·
                refine ⟨4993951878953162351716853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13317205010541766271244941 4993951878953162351716853)
                ·
                  refine ⟨468182988651858970473455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4993951878953162351716853 468182988651858970473455)
                  ·
                    rfl

theorem cell21_2051512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_2051512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051512 prefixEnd_2051512 := by exact prefixLift 2051512
  have htrace : WordTrace (prefixWord ++ tailWord_2051512) baseStart_2051512 baseEnd_2051512 := by
    simpa [prefixWord, tailWord_2051512, baseEnd_2051512] using wordTrace_append hprefix tailTrace_2051512
  have hstable : (prefixWord ++ tailWord_2051512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051512).length < 2 ^ (prefixWord ++ tailWord_2051512).sum := by decide
  have hdescent : baseEnd_2051512 < baseStart_2051512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051546 : List Nat := [3, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_2051546 : Nat := 118140960795 + 2051546 * 2 ^ 59
def prefixEnd_2051546 : Nat := 4983230072969 + 3 ^ 40 * 2051546 * 2
def baseEnd_2051546 : Nat := 468190747915082466906719

theorem tailTrace_2051546 : CollatzResearch.WordTrace tailWord_2051546 prefixEnd_2051546 468190747915082466906719 := by
  unfold tailWord_2051546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18706507456401673251759623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49884019883737795338025661 18706507456401673251759623)
  ·
    refine ⟨28059761184602509877639435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18706507456401673251759623 28059761184602509877639435)
    ·
      refine ⟨42089641776903764816459153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28059761184602509877639435 42089641776903764816459153)
      ·
        refine ⟨31567231332677823612344365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42089641776903764816459153 31567231332677823612344365)
        ·
          refine ⟨11837711749754183854629137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31567231332677823612344365 11837711749754183854629137)
          ·
            refine ⟨8878283812315637890971853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11837711749754183854629137 8878283812315637890971853)
            ·
              refine ⟨3329356429618364209114445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8878283812315637890971853 3329356429618364209114445)
              ·
                refine ⟨1248508661106886578417917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3329356429618364209114445 1248508661106886578417917)
                ·
                  refine ⟨468190747915082466906719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248508661106886578417917 468190747915082466906719)
                  ·
                    rfl

theorem cell21_2051546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_2051546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051546 prefixEnd_2051546 := by exact prefixLift 2051546
  have htrace : WordTrace (prefixWord ++ tailWord_2051546) baseStart_2051546 baseEnd_2051546 := by
    simpa [prefixWord, tailWord_2051546, baseEnd_2051546] using wordTrace_append hprefix tailTrace_2051546
  have hstable : (prefixWord ++ tailWord_2051546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051546).length < 2 ^ (prefixWord ++ tailWord_2051546).sum := by decide
  have hdescent : baseEnd_2051546 < baseStart_2051546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051574 : List Nat := [5, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2051574 : Nat := 118140960795 + 2051574 * 2 ^ 59
def prefixEnd_2051574 : Nat := 4983230072969 + 3 ^ 40 * 2051574 * 2
def baseEnd_2051574 : Nat := 156065712632186880146665

theorem tailTrace_2051574 : CollatzResearch.WordTrace tailWord_2051574 prefixEnd_2051574 156065712632186880146665 := by
  unfold tailWord_2051574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676690691844078361816111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49884700713003502526038517 4676690691844078361816111)
  ·
    refine ⟨7015036037766117542724167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4676690691844078361816111 7015036037766117542724167)
    ·
      refine ⟨10522554056649176314086251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7015036037766117542724167 10522554056649176314086251)
      ·
        refine ⟨15783831084973764471129377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10522554056649176314086251 15783831084973764471129377)
        ·
          refine ⟨11837873313730323353347033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15783831084973764471129377 11837873313730323353347033)
          ·
            refine ⟨8878404985297742515010275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11837873313730323353347033 8878404985297742515010275)
            ·
              refine ⟨13317607477946613772515413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8878404985297742515010275 13317607477946613772515413)
              ·
                refine ⟨156065712632186880146665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13317607477946613772515413 156065712632186880146665)
                ·
                  rfl

theorem cell21_2051574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2051574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051574 prefixEnd_2051574 := by exact prefixLift 2051574
  have htrace : WordTrace (prefixWord ++ tailWord_2051574) baseStart_2051574 baseEnd_2051574 := by
    simpa [prefixWord, tailWord_2051574, baseEnd_2051574] using wordTrace_append hprefix tailTrace_2051574
  have hstable : (prefixWord ++ tailWord_2051574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051574).length < 2 ^ (prefixWord ++ tailWord_2051574).sum := by decide
  have hdescent : baseEnd_2051574 < baseStart_2051574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051670 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2051670 : Nat := 118140960795 + 2051670 * 2 ^ 59
def prefixEnd_2051670 : Nat := 4983230072969 + 3 ^ 40 * 2051670 * 2
def baseEnd_2051670 : Nat := 468219046404485806839799

theorem tailTrace_2051670 : CollatzResearch.WordTrace tailWord_2051670 prefixEnd_2051670 468219046404485806839799 := by
  unfold tailWord_2051670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4676909529822341386534529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49887034984771641456368309 4676909529822341386534529)
  ·
    refine ⟨3507682147366756039900897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4676909529822341386534529 3507682147366756039900897)
    ·
      refine ⟨2630761610525067029925673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3507682147366756039900897 2630761610525067029925673)
      ·
        refine ⟨1973071207893800272444255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2630761610525067029925673 1973071207893800272444255)
        ·
          refine ⟨2959606811840700408666383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973071207893800272444255 2959606811840700408666383)
          ·
            refine ⟨4439410217761050612999575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959606811840700408666383 4439410217761050612999575)
            ·
              refine ⟨6659115326641575919499363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439410217761050612999575 6659115326641575919499363)
              ·
                refine ⟨9988672989962363879249045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659115326641575919499363 9988672989962363879249045)
                ·
                  refine ⟨468219046404485806839799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9988672989962363879249045 468219046404485806839799)
                  ·
                    rfl

theorem cell21_2051670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2051670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051670 prefixEnd_2051670 := by exact prefixLift 2051670
  have htrace : WordTrace (prefixWord ++ tailWord_2051670) baseStart_2051670 baseEnd_2051670 := by
    simpa [prefixWord, tailWord_2051670, baseEnd_2051670] using wordTrace_append hprefix tailTrace_2051670
  have hstable : (prefixWord ++ tailWord_2051670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051670).length < 2 ^ (prefixWord ++ tailWord_2051670).sum := by decide
  have hdescent : baseEnd_2051670 < baseStart_2051670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051681 : List Nat := [1, 2, 3, 1, 1, 3, 1, 6, 3]
def baseStart_2051681 : Nat := 118140960795 + 2051681 * 2 ^ 59
def prefixEnd_2051681 : Nat := 4983230072969 + 3 ^ 40 * 2051681 * 2
def baseEnd_2051681 : Nat := 468221556754352232156443

theorem tailTrace_2051681 : CollatzResearch.WordTrace tailWord_2051681 prefixEnd_2051681 468221556754352232156443 := by
  unfold tailWord_2051681
  simp only [CollatzResearch.WordTrace]
  refine ⟨74830953680117611063202897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49887302453411740708801931 74830953680117611063202897)
  ·
    refine ⟨56123215260088208297402173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74830953680117611063202897 56123215260088208297402173)
    ·
      refine ⟨21046205722533078111525815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56123215260088208297402173 21046205722533078111525815)
      ·
        refine ⟨31569308583799617167288723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21046205722533078111525815 31569308583799617167288723)
        ·
          refine ⟨47353962875699425750933085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31569308583799617167288723 47353962875699425750933085)
          ·
            refine ⟨17757736078387284656599907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47353962875699425750933085 17757736078387284656599907)
            ·
              refine ⟨26636604117580926984899861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17757736078387284656599907 26636604117580926984899861)
              ·
                refine ⟨1248590818011605952417181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26636604117580926984899861 1248590818011605952417181)
                ·
                  refine ⟨468221556754352232156443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248590818011605952417181 468221556754352232156443)
                  ·
                    rfl

theorem cell21_2051681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_2051681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051681 prefixEnd_2051681 := by exact prefixLift 2051681
  have htrace : WordTrace (prefixWord ++ tailWord_2051681) baseStart_2051681 baseEnd_2051681 := by
    simpa [prefixWord, tailWord_2051681, baseEnd_2051681] using wordTrace_append hprefix tailTrace_2051681
  have hstable : (prefixWord ++ tailWord_2051681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051681).length < 2 ^ (prefixWord ++ tailWord_2051681).sum := by decide
  have hdescent : baseEnd_2051681 < baseStart_2051681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051726 : List Nat := [4, 1, 1, 3, 1, 4, 7]
def baseStart_2051726 : Nat := 118140960795 + 2051726 * 2 ^ 59
def prefixEnd_2051726 : Nat := 4983230072969 + 3 ^ 40 * 2051726 * 2
def baseEnd_2051726 : Nat := 52025758485271350434039

theorem tailTrace_2051726 : CollatzResearch.WordTrace tailWord_2051726 prefixEnd_2051726 52025758485271350434039 := by
  unfold tailWord_2051726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354074370619322968573879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49888396643303055832394021 9354074370619322968573879)
  ·
    refine ⟨14031111555928984452860819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9354074370619322968573879 14031111555928984452860819)
    ·
      refine ⟨21046667333893476679291229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14031111555928984452860819 21046667333893476679291229)
      ·
        refine ⟨7892500250210053754734211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21046667333893476679291229 7892500250210053754734211)
        ·
          refine ⟨11838750375315080632101317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7892500250210053754734211 11838750375315080632101317)
          ·
            refine ⟨2219765695371577618518997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11838750375315080632101317 2219765695371577618518997)
            ·
              refine ⟨52025758485271350434039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2219765695371577618518997 52025758485271350434039)
              ·
                rfl

theorem cell21_2051726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 7].length) (baseStart_2051726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051726 prefixEnd_2051726 := by exact prefixLift 2051726
  have htrace : WordTrace (prefixWord ++ tailWord_2051726) baseStart_2051726 baseEnd_2051726 := by
    simpa [prefixWord, tailWord_2051726, baseEnd_2051726] using wordTrace_append hprefix tailTrace_2051726
  have hstable : (prefixWord ++ tailWord_2051726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051726).length < 2 ^ (prefixWord ++ tailWord_2051726).sum := by decide
  have hdescent : baseEnd_2051726 < baseStart_2051726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051732 : List Nat := [2, 4, 2, 2, 2, 1, 3, 2, 3]
def baseStart_2051732 : Nat := 118140960795 + 2051732 * 2 ^ 59
def prefixEnd_2051732 : Nat := 4983230072969 + 3 ^ 40 * 2051732 * 2
def baseEnd_2051732 : Nat := 468233195649187476806339

theorem tailTrace_2051732 : CollatzResearch.WordTrace tailWord_2051732 prefixEnd_2051732 468233195649187476806339 := by
  unfold tailWord_2051732
  simp only [CollatzResearch.WordTrace]
  refine ⟨37416406901466423386654725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49888542535288564515539633 37416406901466423386654725)
  ·
    refine ⟨7015576294024954384997761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37416406901466423386654725 7015576294024954384997761)
    ·
      refine ⟨5261682220518715788748321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7015576294024954384997761 5261682220518715788748321)
      ·
        refine ⟨3946261665389036841561241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5261682220518715788748321 3946261665389036841561241)
        ·
          refine ⟨2959696249041777631170931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3946261665389036841561241 2959696249041777631170931)
          ·
            refine ⟨4439544373562666446756397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959696249041777631170931 4439544373562666446756397)
            ·
              refine ⟨1664829140085999917533649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4439544373562666446756397 1664829140085999917533649)
              ·
                refine ⟨1248621855064499938150237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1664829140085999917533649 1248621855064499938150237)
                ·
                  refine ⟨468233195649187476806339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248621855064499938150237 468233195649187476806339)
                  ·
                    rfl

theorem cell21_2051732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_2051732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051732 prefixEnd_2051732 := by exact prefixLift 2051732
  have htrace : WordTrace (prefixWord ++ tailWord_2051732) baseStart_2051732 baseEnd_2051732 := by
    simpa [prefixWord, tailWord_2051732, baseEnd_2051732] using wordTrace_append hprefix tailTrace_2051732
  have hstable : (prefixWord ++ tailWord_2051732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051732).length < 2 ^ (prefixWord ++ tailWord_2051732).sum := by decide
  have hdescent : baseEnd_2051732 < baseStart_2051732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051743 : List Nat := [1, 1, 2, 7, 1, 1, 2, 6]
def baseStart_2051743 : Nat := 118140960795 + 2051743 * 2 ^ 59
def prefixEnd_2051743 : Nat := 4983230072969 + 3 ^ 40 * 2051743 * 2
def baseEnd_2051743 : Nat := 156078568666351300707661

theorem tailTrace_2051743 : CollatzResearch.WordTrace tailWord_2051743 prefixEnd_2051743 156078568666351300707661 := by
  unfold tailWord_2051743
  simp only [CollatzResearch.WordTrace]
  refine ⟨74833215005892995651959883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49888810003928663767973255 74833215005892995651959883)
  ·
    refine ⟨112249822508839493477939825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74833215005892995651959883 112249822508839493477939825)
    ·
      refine ⟨84187366881629620108454869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112249822508839493477939825 84187366881629620108454869)
      ·
        refine ⟨1973141411288194221291911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 84187366881629620108454869 1973141411288194221291911)
        ·
          refine ⟨2959712116932291331937867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973141411288194221291911 2959712116932291331937867)
          ·
            refine ⟨4439568175398436997906801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959712116932291331937867 4439568175398436997906801)
            ·
              refine ⟨3329676131548827748430101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4439568175398436997906801 3329676131548827748430101)
              ·
                refine ⟨156078568666351300707661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3329676131548827748430101 156078568666351300707661)
                ·
                  rfl

theorem cell21_2051743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 6].length) (baseStart_2051743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051743 prefixEnd_2051743 := by exact prefixLift 2051743
  have htrace : WordTrace (prefixWord ++ tailWord_2051743) baseStart_2051743 baseEnd_2051743 := by
    simpa [prefixWord, tailWord_2051743, baseEnd_2051743] using wordTrace_append hprefix tailTrace_2051743
  have hstable : (prefixWord ++ tailWord_2051743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051743).length < 2 ^ (prefixWord ++ tailWord_2051743).sum := by decide
  have hdescent : baseEnd_2051743 < baseStart_2051743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051802 : List Nat := [3, 1, 1, 2, 2, 5, 1, 6]
def baseStart_2051802 : Nat := 118140960795 + 2051802 * 2 ^ 59
def prefixEnd_2051802 : Nat := 4983230072969 + 3 ^ 40 * 2051802 * 2
def baseEnd_2051802 : Nat := 156083056867627636879843

theorem tailTrace_2051802 : CollatzResearch.WordTrace tailWord_2051802 prefixEnd_2051802 156083056867627636879843 := by
  unfold tailWord_2051802
  simp only [CollatzResearch.WordTrace]
  refine ⟨18708841728169812182089415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49890244608452832485571773 18708841728169812182089415)
  ·
    refine ⟨28063262592254718273134123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18708841728169812182089415 28063262592254718273134123)
    ·
      refine ⟨42094893888382077409701185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28063262592254718273134123 42094893888382077409701185)
      ·
        refine ⟨31571170416286558057275889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42094893888382077409701185 31571170416286558057275889)
        ·
          refine ⟨23678377812214918542956917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31571170416286558057275889 23678377812214918542956917)
          ·
            refine ⟨2219847919895148613402211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23678377812214918542956917 2219847919895148613402211)
            ·
              refine ⟨3329771879842722920103317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2219847919895148613402211 3329771879842722920103317)
              ·
                refine ⟨156083056867627636879843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3329771879842722920103317 156083056867627636879843)
                ·
                  rfl

theorem cell21_2051802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_2051802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051802 prefixEnd_2051802 := by exact prefixLift 2051802
  have htrace : WordTrace (prefixWord ++ tailWord_2051802) baseStart_2051802 baseEnd_2051802 := by
    simpa [prefixWord, tailWord_2051802, baseEnd_2051802] using wordTrace_append hprefix tailTrace_2051802
  have hstable : (prefixWord ++ tailWord_2051802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051802).length < 2 ^ (prefixWord ++ tailWord_2051802).sum := by decide
  have hdescent : baseEnd_2051802 < baseStart_2051802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051816 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_2051816 : Nat := 118140960795 + 2051816 * 2 ^ 59
def prefixEnd_2051816 : Nat := 4983230072969 + 3 ^ 40 * 2051816 * 2
def baseEnd_2051816 : Nat := 468252365593621997406167

theorem tailTrace_2051816 : CollatzResearch.WordTrace tailWord_2051816 prefixEnd_2051816 468252365593621997406167 := by
  unfold tailWord_2051816
  simp only [CollatzResearch.WordTrace]
  refine ⟨37417938767314264559683651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49890585023085686079578201 37417938767314264559683651)
  ·
    refine ⟨56126908150971396839525477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37417938767314264559683651 56126908150971396839525477)
    ·
      refine ⟨10523795278307136907411027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56126908150971396839525477 10523795278307136907411027)
      ·
        refine ⟨15785692917460705361116541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10523795278307136907411027 15785692917460705361116541)
        ·
          refine ⟨5919634844047764510418703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15785692917460705361116541 5919634844047764510418703)
          ·
            refine ⟨8879452266071646765628055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919634844047764510418703 8879452266071646765628055)
            ·
              refine ⟨13319178399107470148442083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879452266071646765628055 13319178399107470148442083)
              ·
                refine ⟨19978767598661205222663125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13319178399107470148442083 19978767598661205222663125)
                ·
                  refine ⟨468252365593621997406167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19978767598661205222663125 468252365593621997406167)
                  ·
                    rfl

theorem cell21_2051816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_2051816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051816 prefixEnd_2051816 := by exact prefixLift 2051816
  have htrace : WordTrace (prefixWord ++ tailWord_2051816) baseStart_2051816 baseEnd_2051816 := by
    simpa [prefixWord, tailWord_2051816, baseEnd_2051816] using wordTrace_append hprefix tailTrace_2051816
  have hstable : (prefixWord ++ tailWord_2051816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051816).length < 2 ^ (prefixWord ++ tailWord_2051816).sum := by decide
  have hdescent : baseEnd_2051816 < baseStart_2051816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2051870 : List Nat := [4, 3, 2, 2, 2, 1, 2, 5]
def baseStart_2051870 : Nat := 118140960795 + 2051870 * 2 ^ 59
def prefixEnd_2051870 : Nat := 4983230072969 + 3 ^ 40 * 2051870 * 2
def baseEnd_2051870 : Nat := 156088229709776634502019

theorem tailTrace_2051870 : CollatzResearch.WordTrace tailWord_2051870 prefixEnd_2051870 156088229709776634502019 := by
  unfold tailWord_2051870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354730884554112042729133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49891898050955264227888709 9354730884554112042729133)
  ·
    refine ⟨3508024081707792016023425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9354730884554112042729133 3508024081707792016023425)
    ·
      refine ⟨2631018061280844012017569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3508024081707792016023425 2631018061280844012017569)
      ·
        refine ⟨1973263545960633009013177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2631018061280844012017569 1973263545960633009013177)
        ·
          refine ⟨1479947659470474756759883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1973263545960633009013177 1479947659470474756759883)
          ·
            refine ⟨2219921489205712135139825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1479947659470474756759883 2219921489205712135139825)
            ·
              refine ⟨1664941116904284101354869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2219921489205712135139825 1664941116904284101354869)
              ·
                refine ⟨156088229709776634502019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1664941116904284101354869 156088229709776634502019)
                ·
                  rfl

theorem cell21_2051870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_2051870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2051870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2051870 prefixEnd_2051870 := by exact prefixLift 2051870
  have htrace : WordTrace (prefixWord ++ tailWord_2051870) baseStart_2051870 baseEnd_2051870 := by
    simpa [prefixWord, tailWord_2051870, baseEnd_2051870] using wordTrace_append hprefix tailTrace_2051870
  have hstable : (prefixWord ++ tailWord_2051870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2051870).length < 2 ^ (prefixWord ++ tailWord_2051870).sum := by decide
  have hdescent : baseEnd_2051870 < baseStart_2051870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2051870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052027 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 5]
def baseStart_2052027 : Nat := 118140960795 + 2052027 * 2 ^ 59
def prefixEnd_2052027 : Nat := 4983230072969 + 3 ^ 40 * 2052027 * 2
def baseEnd_2052027 : Nat := 468300518668332519389069

theorem tailTrace_2052027 : CollatzResearch.WordTrace tailWord_2052027 prefixEnd_2052027 468300518668332519389069 := by
  unfold tailWord_2052027
  simp only [CollatzResearch.WordTrace]
  refine ⟨74843573336864112155298335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49895715557909408103532223 74843573336864112155298335)
  ·
    refine ⟨112265360005296168232947503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74843573336864112155298335 112265360005296168232947503)
    ·
      refine ⟨168398040007944252349421255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112265360005296168232947503 168398040007944252349421255)
      ·
        refine ⟨252597060011916378524131883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168398040007944252349421255 252597060011916378524131883)
        ·
          refine ⟨378895590017874567786197825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252597060011916378524131883 378895590017874567786197825)
          ·
            refine ⟨284171692513405925839648369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378895590017874567786197825 284171692513405925839648369)
            ·
              refine ⟨213128769385054444379736277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284171692513405925839648369 213128769385054444379736277)
              ·
                refine ⟨4995205532462213540150069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 213128769385054444379736277 4995205532462213540150069)
                ·
                  refine ⟨468300518668332519389069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4995205532462213540150069 468300518668332519389069)
                  ·
                    rfl

theorem cell21_2052027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_2052027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052027 prefixEnd_2052027 := by exact prefixLift 2052027
  have htrace : WordTrace (prefixWord ++ tailWord_2052027) baseStart_2052027 baseEnd_2052027 := by
    simpa [prefixWord, tailWord_2052027, baseEnd_2052027] using wordTrace_append hprefix tailTrace_2052027
  have hstable : (prefixWord ++ tailWord_2052027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052027).length < 2 ^ (prefixWord ++ tailWord_2052027).sum := by decide
  have hdescent : baseEnd_2052027 < baseStart_2052027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052044 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_2052044 : Nat := 118140960795 + 2052044 * 2 ^ 59
def prefixEnd_2052044 : Nat := 4983230072969 + 3 ^ 40 * 2052044 * 2
def baseEnd_2052044 : Nat := 468304398299944267605701

theorem tailTrace_2052044 : CollatzResearch.WordTrace tailWord_2052044 prefixEnd_2052044 468304398299944267605701 := by
  unfold tailWord_2052044
  simp only [CollatzResearch.WordTrace]
  refine ⟨37422096688901262029333593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49896128918535016039111457 37422096688901262029333593)
  ·
    refine ⟨28066572516675946522000195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37422096688901262029333593 28066572516675946522000195)
    ·
      refine ⟨42099858775013919783000293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28066572516675946522000195 42099858775013919783000293)
      ·
        refine ⟨7893723520315109959312555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42099858775013919783000293 7893723520315109959312555)
        ·
          refine ⟨11840585280472664938968833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7893723520315109959312555 11840585280472664938968833)
          ·
            refine ⟨8880438960354498704226625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11840585280472664938968833 8880438960354498704226625)
            ·
              refine ⟨6660329220265874028169969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8880438960354498704226625 6660329220265874028169969)
              ·
                refine ⟨4995246915199405521127477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6660329220265874028169969 4995246915199405521127477)
                ·
                  refine ⟨468304398299944267605701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4995246915199405521127477 468304398299944267605701)
                  ·
                    rfl

theorem cell21_2052044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_2052044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052044 prefixEnd_2052044 := by exact prefixLift 2052044
  have htrace : WordTrace (prefixWord ++ tailWord_2052044) baseStart_2052044 baseEnd_2052044 := by
    simpa [prefixWord, tailWord_2052044, baseEnd_2052044] using wordTrace_append hprefix tailTrace_2052044
  have hstable : (prefixWord ++ tailWord_2052044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052044).length < 2 ^ (prefixWord ++ tailWord_2052044).sum := by decide
  have hdescent : baseEnd_2052044 < baseStart_2052044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052089 : List Nat := [1, 2, 1, 3, 1, 5, 2, 6]
def baseStart_2052089 : Nat := 118140960795 + 2052089 * 2 ^ 59
def prefixEnd_2052089 : Nat := 4983230072969 + 3 ^ 40 * 2052089 * 2
def baseEnd_2052089 : Nat := 156104889304344729785203

theorem tailTrace_2052089 : CollatzResearch.WordTrace tailWord_2052089 prefixEnd_2052089 156104889304344729785203 := by
  unfold tailWord_2052089
  simp only [CollatzResearch.WordTrace]
  refine ⟨74845834662639496744055321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49897223108426331162703547 74845834662639496744055321)
  ·
    refine ⟨56134375996979622558041491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74845834662639496744055321 56134375996979622558041491)
    ·
      refine ⟨84201563995469433837062237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56134375996979622558041491 84201563995469433837062237)
      ·
        refine ⟨31575586498301037688898339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84201563995469433837062237 31575586498301037688898339)
        ·
          refine ⟨47363379747451556533347509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31575586498301037688898339 47363379747451556533347509)
          ·
            refine ⟨4440316851323583425001329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47363379747451556533347509 4440316851323583425001329)
            ·
              refine ⟨3330237638492687568750997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440316851323583425001329 3330237638492687568750997)
              ·
                refine ⟨156104889304344729785203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3330237638492687568750997 156104889304344729785203)
                ·
                  rfl

theorem cell21_2052089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 6].length) (baseStart_2052089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052089 prefixEnd_2052089 := by exact prefixLift 2052089
  have htrace : WordTrace (prefixWord ++ tailWord_2052089) baseStart_2052089 baseEnd_2052089 := by
    simpa [prefixWord, tailWord_2052089, baseEnd_2052089] using wordTrace_append hprefix tailTrace_2052089
  have hstable : (prefixWord ++ tailWord_2052089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052089).length < 2 ^ (prefixWord ++ tailWord_2052089).sum := by decide
  have hdescent : baseEnd_2052089 < baseStart_2052089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052258 : List Nat := [3, 3, 1, 3, 1, 2, 2, 6]
def baseStart_2052258 : Nat := 118140960795 + 2052258 * 2 ^ 59
def prefixEnd_2052258 : Nat := 4983230072969 + 3 ^ 40 * 2052258 * 2
def baseEnd_2052258 : Nat := 156117745338509150346199

theorem tailTrace_2052258 : CollatzResearch.WordTrace tailWord_2052258 prefixEnd_2052258 156117745338509150346199 := by
  unfold tailWord_2052258
  simp only [CollatzResearch.WordTrace]
  refine ⟨18712999649756809651739357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49901332399351492404638285 18712999649756809651739357)
  ·
    refine ⟨7017374868658803619402259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18712999649756809651739357 7017374868658803619402259)
    ·
      refine ⟨10526062302988205429103389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7017374868658803619402259 10526062302988205429103389)
      ·
        refine ⟨3947273363620577035913771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10526062302988205429103389 3947273363620577035913771)
        ·
          refine ⟨5920910045430865553870657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3947273363620577035913771 5920910045430865553870657)
          ·
            refine ⟨4440682534073149165402993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5920910045430865553870657 4440682534073149165402993)
            ·
              refine ⟨3330511900554861874052245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440682534073149165402993 3330511900554861874052245)
              ·
                refine ⟨156117745338509150346199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3330511900554861874052245 156117745338509150346199)
                ·
                  rfl

theorem cell21_2052258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_2052258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052258 prefixEnd_2052258 := by exact prefixLift 2052258
  have htrace : WordTrace (prefixWord ++ tailWord_2052258) baseStart_2052258 baseEnd_2052258 := by
    simpa [prefixWord, tailWord_2052258, baseEnd_2052258] using wordTrace_append hprefix tailTrace_2052258
  have hstable : (prefixWord ++ tailWord_2052258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052258).length < 2 ^ (prefixWord ++ tailWord_2052258).sum := by decide
  have hdescent : baseEnd_2052258 < baseStart_2052258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052306 : List Nat := [3, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_2052306 : Nat := 118140960795 + 2052306 * 2 ^ 59
def prefixEnd_2052306 : Nat := 4983230072969 + 3 ^ 40 * 2052306 * 2
def baseEnd_2052306 : Nat := 468364190269490034238499

theorem tailTrace_2052306 : CollatzResearch.WordTrace tailWord_2052306 prefixEnd_2052306 468364190269490034238499 := by
  unfold tailWord_2052306
  simp only [CollatzResearch.WordTrace]
  refine ⟨18713437325713335701176193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49902499535235561869803181 18713437325713335701176193)
  ·
    refine ⟨14035077994285001775882145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18713437325713335701176193 14035077994285001775882145)
    ·
      refine ⟨10526308495713751331911609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14035077994285001775882145 10526308495713751331911609)
      ·
        refine ⟨7894731371785313498933707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10526308495713751331911609 7894731371785313498933707)
        ·
          refine ⟨11842097057677970248400561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7894731371785313498933707 11842097057677970248400561)
          ·
            refine ⟨8881572793258477686300421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11842097057677970248400561 8881572793258477686300421)
            ·
              refine ⟨1665294898735964566181329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8881572793258477686300421 1665294898735964566181329)
              ·
                refine ⟨1248971174051973424635997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665294898735964566181329 1248971174051973424635997)
                ·
                  refine ⟨468364190269490034238499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1248971174051973424635997 468364190269490034238499)
                  ·
                    rfl

theorem cell21_2052306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_2052306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052306 prefixEnd_2052306 := by exact prefixLift 2052306
  have htrace : WordTrace (prefixWord ++ tailWord_2052306) baseStart_2052306 baseEnd_2052306 := by
    simpa [prefixWord, tailWord_2052306, baseEnd_2052306] using wordTrace_append hprefix tailTrace_2052306
  have hstable : (prefixWord ++ tailWord_2052306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052306).length < 2 ^ (prefixWord ++ tailWord_2052306).sum := by decide
  have hdescent : baseEnd_2052306 < baseStart_2052306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052331 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 5]
def baseStart_2052331 : Nat := 118140960795 + 2052331 * 2 ^ 59
def prefixEnd_2052331 : Nat := 4983230072969 + 3 ^ 40 * 2052331 * 2
def baseEnd_2052331 : Nat := 468369895610095546321781

theorem tailTrace_2052331 : CollatzResearch.WordTrace tailWord_2052331 prefixEnd_2052331 468369895610095546321781 := by
  unfold tailWord_2052331
  simp only [CollatzResearch.WordTrace]
  refine ⟨74854661127762772074364847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49903107418508514716243231 74854661127762772074364847)
  ·
    refine ⟨112281991691644158111547271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74854661127762772074364847 112281991691644158111547271)
    ·
      refine ⟨168422987537466237167320907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112281991691644158111547271 168422987537466237167320907)
      ·
        refine ⟨252634481306199355750981361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168422987537466237167320907 252634481306199355750981361)
        ·
          refine ⟨189475860979649516813236021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252634481306199355750981361 189475860979649516813236021)
          ·
            refine ⟨17763361966842142201240877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189475860979649516813236021 17763361966842142201240877)
            ·
              refine ⟨6661260737565803325465329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17763361966842142201240877 6661260737565803325465329)
              ·
                refine ⟨4995945553174352494098997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6661260737565803325465329 4995945553174352494098997)
                ·
                  refine ⟨468369895610095546321781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4995945553174352494098997 468369895610095546321781)
                  ·
                    rfl

theorem cell21_2052331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_2052331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052331 prefixEnd_2052331 := by exact prefixLift 2052331
  have htrace : WordTrace (prefixWord ++ tailWord_2052331) baseStart_2052331 baseEnd_2052331 := by
    simpa [prefixWord, tailWord_2052331, baseEnd_2052331] using wordTrace_append hprefix tailTrace_2052331
  have hstable : (prefixWord ++ tailWord_2052331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052331).length < 2 ^ (prefixWord ++ tailWord_2052331).sum := by decide
  have hdescent : baseEnd_2052331 < baseStart_2052331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052376 : List Nat := [2, 1, 2, 3, 1, 2, 2, 8]
def baseStart_2052376 : Nat := 118140960795 + 2052376 * 2 ^ 59
def prefixEnd_2052376 : Nat := 4983230072969 + 3 ^ 40 * 2052376 * 2
def baseEnd_2052376 : Nat := 156126721741061822690563

theorem tailTrace_2052376 : CollatzResearch.WordTrace tailWord_2052376 prefixEnd_2052376 156126721741061822690563 := by
  unfold tailWord_2052376
  simp only [CollatzResearch.WordTrace]
  refine ⟨37428151206299872379876491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49904201608399829839835321 37428151206299872379876491)
  ·
    refine ⟨56142226809449808569814737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37428151206299872379876491 56142226809449808569814737)
    ·
      refine ⟨42106670107087356427361053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56142226809449808569814737 42106670107087356427361053)
      ·
        refine ⟨15790001290157758660260395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42106670107087356427361053 15790001290157758660260395)
        ·
          refine ⟨23685001935236637990390593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15790001290157758660260395 23685001935236637990390593)
          ·
            refine ⟨17763751451427478492792945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23685001935236637990390593 17763751451427478492792945)
            ·
              refine ⟨13322813588570608869594709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17763751451427478492792945 13322813588570608869594709)
              ·
                refine ⟨156126721741061822690563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13322813588570608869594709 156126721741061822690563)
                ·
                  rfl

theorem cell21_2052376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_2052376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052376 prefixEnd_2052376 := by exact prefixLift 2052376
  have htrace : WordTrace (prefixWord ++ tailWord_2052376) baseStart_2052376 baseEnd_2052376 := by
    simpa [prefixWord, tailWord_2052376, baseEnd_2052376] using wordTrace_append hprefix tailTrace_2052376
  have hstable : (prefixWord ++ tailWord_2052376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052376).length < 2 ^ (prefixWord ++ tailWord_2052376).sum := by decide
  have hdescent : baseEnd_2052376 < baseStart_2052376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052424 : List Nat := [2, 1, 3, 1, 1, 2, 2, 6, 3]
def baseStart_2052424 : Nat := 118140960795 + 2052424 * 2 ^ 59
def prefixEnd_2052424 : Nat := 4983230072969 + 3 ^ 40 * 2052424 * 2
def baseEnd_2052424 : Nat := 468391119477148051271591

theorem tailTrace_2052424 : CollatzResearch.WordTrace tailWord_2052424 prefixEnd_2052424 468391119477148051271591 := by
  unfold tailWord_2052424
  simp only [CollatzResearch.WordTrace]
  refine ⟨37429026558212924478750163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49905368744283899305000217 37429026558212924478750163)
  ·
    refine ⟨56143539837319386718125245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37429026558212924478750163 56143539837319386718125245)
    ·
      refine ⟨21053827438994770019296967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56143539837319386718125245 21053827438994770019296967)
      ·
        refine ⟨31580741158492155028945451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21053827438994770019296967 31580741158492155028945451)
        ·
          refine ⟨47371111737738232543418177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31580741158492155028945451 47371111737738232543418177)
          ·
            refine ⟨35528333803303674407563633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47371111737738232543418177 35528333803303674407563633)
            ·
              refine ⟨26646250352477755805672725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35528333803303674407563633 26646250352477755805672725)
              ·
                refine ⟨1249042985272394803390909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26646250352477755805672725 1249042985272394803390909)
                ·
                  refine ⟨468391119477148051271591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249042985272394803390909 468391119477148051271591)
                  ·
                    rfl

theorem cell21_2052424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_2052424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052424 prefixEnd_2052424 := by exact prefixLift 2052424
  have htrace : WordTrace (prefixWord ++ tailWord_2052424) baseStart_2052424 baseEnd_2052424 := by
    simpa [prefixWord, tailWord_2052424, baseEnd_2052424] using wordTrace_append hprefix tailTrace_2052424
  have hstable : (prefixWord ++ tailWord_2052424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052424).length < 2 ^ (prefixWord ++ tailWord_2052424).sum := by decide
  have hdescent : baseEnd_2052424 < baseStart_2052424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052452 : List Nat := [2, 3, 1, 1, 3, 1, 1, 9]
def baseStart_2052452 : Nat := 118140960795 + 2052452 * 2 ^ 59
def prefixEnd_2052452 : Nat := 4983230072969 + 3 ^ 40 * 2052452 * 2
def baseEnd_2052452 : Nat := 156132503152875408268289

theorem tailTrace_2052452 : CollatzResearch.WordTrace tailWord_2052452 prefixEnd_2052452 156132503152875408268289 := by
  unfold tailWord_2052452
  simp only [CollatzResearch.WordTrace]
  refine ⟨37429537180162204869759805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49906049573549606493013073 37429537180162204869759805)
  ·
    refine ⟨14036076442560826826159927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37429537180162204869759805 14036076442560826826159927)
    ·
      refine ⟨21054114663841240239239891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14036076442560826826159927 21054114663841240239239891)
      ·
        refine ⟨31581171995761860358859837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21054114663841240239239891 31581171995761860358859837)
        ·
          refine ⟨11842939498410697634572439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31581171995761860358859837 11842939498410697634572439)
          ·
            refine ⟨17764409247616046451858659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11842939498410697634572439 17764409247616046451858659)
            ·
              refine ⟨26646613871424069677787989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17764409247616046451858659 26646613871424069677787989)
              ·
                refine ⟨156132503152875408268289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26646613871424069677787989 156132503152875408268289)
                ·
                  rfl

theorem cell21_2052452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_2052452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052452 prefixEnd_2052452 := by exact prefixLift 2052452
  have htrace : WordTrace (prefixWord ++ tailWord_2052452) baseStart_2052452 baseEnd_2052452 := by
    simpa [prefixWord, tailWord_2052452, baseEnd_2052452] using wordTrace_append hprefix tailTrace_2052452
  have hstable : (prefixWord ++ tailWord_2052452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052452).length < 2 ^ (prefixWord ++ tailWord_2052452).sum := by decide
  have hdescent : baseEnd_2052452 < baseStart_2052452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052514 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_2052514 : Nat := 118140960795 + 2052514 * 2 ^ 59
def prefixEnd_2052514 : Nat := 4983230072969 + 3 ^ 40 * 2052514 * 2
def baseEnd_2052514 : Nat := 468411658703327894771407

theorem tailTrace_2052514 : CollatzResearch.WordTrace tailWord_2052514 prefixEnd_2052514 468411658703327894771407 := by
  unfold tailWord_2052514
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715333921524948582069149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49907557124066529552184397 18715333921524948582069149)
  ·
    refine ⟨7018250220571855718275931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18715333921524948582069149 7018250220571855718275931)
    ·
      refine ⟨10527375330857783577413897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7018250220571855718275931 10527375330857783577413897)
      ·
        refine ⟨7895531498143337683060423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10527375330857783577413897 7895531498143337683060423)
        ·
          refine ⟨11843297247215006524590635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7895531498143337683060423 11843297247215006524590635)
          ·
            refine ⟨17764945870822509786885953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11843297247215006524590635 17764945870822509786885953)
            ·
              refine ⟨13323709403116882340164465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17764945870822509786885953 13323709403116882340164465)
              ·
                refine ⟨9992782052337661755123349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13323709403116882340164465 9992782052337661755123349)
                ·
                  refine ⟨468411658703327894771407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9992782052337661755123349 468411658703327894771407)
                  ·
                    rfl

theorem cell21_2052514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_2052514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052514 prefixEnd_2052514 := by exact prefixLift 2052514
  have htrace : WordTrace (prefixWord ++ tailWord_2052514) baseStart_2052514 baseEnd_2052514 := by
    simpa [prefixWord, tailWord_2052514, baseEnd_2052514] using wordTrace_append hprefix tailTrace_2052514
  have hstable : (prefixWord ++ tailWord_2052514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052514).length < 2 ^ (prefixWord ++ tailWord_2052514).sum := by decide
  have hdescent : baseEnd_2052514 < baseStart_2052514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052562 : List Nat := [3, 2, 2, 4, 1, 1, 1, 7]
def baseStart_2052562 : Nat := 118140960795 + 2052562 * 2 ^ 59
def prefixEnd_2052562 : Nat := 4983230072969 + 3 ^ 40 * 2052562 * 2
def baseEnd_2052562 : Nat := 156140870985763492657103

theorem tailTrace_2052562 : CollatzResearch.WordTrace tailWord_2052562 prefixEnd_2052562 156140870985763492657103 := by
  unfold tailWord_2052562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18715771597481474631505985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49908724259950599017349293 18715771597481474631505985)
  ·
    refine ⟨14036828698111105973629489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18715771597481474631505985 14036828698111105973629489)
    ·
      refine ⟨10527621523583329480222117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14036828698111105973629489 10527621523583329480222117)
      ·
        refine ⟨1973929035671874277541647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10527621523583329480222117 1973929035671874277541647)
        ·
          refine ⟨2960893553507811416312471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1973929035671874277541647 2960893553507811416312471)
          ·
            refine ⟨4441340330261717124468707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960893553507811416312471 4441340330261717124468707)
            ·
              refine ⟨6662010495392575686703061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441340330261717124468707 6662010495392575686703061)
              ·
                refine ⟨156140870985763492657103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6662010495392575686703061 156140870985763492657103)
                ·
                  rfl

theorem cell21_2052562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_2052562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052562 prefixEnd_2052562 := by exact prefixLift 2052562
  have htrace : WordTrace (prefixWord ++ tailWord_2052562) baseStart_2052562 baseEnd_2052562 := by
    simpa [prefixWord, tailWord_2052562, baseEnd_2052562] using wordTrace_append hprefix tailTrace_2052562
  have hstable : (prefixWord ++ tailWord_2052562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052562).length < 2 ^ (prefixWord ++ tailWord_2052562).sum := by decide
  have hdescent : baseEnd_2052562 < baseStart_2052562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052590 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_2052590 : Nat := 118140960795 + 2052590 * 2 ^ 59
def prefixEnd_2052590 : Nat := 4983230072969 + 3 ^ 40 * 2052590 * 2
def baseEnd_2052590 : Nat := 468429002938768651504585

theorem tailTrace_2052590 : CollatzResearch.WordTrace tailWord_2052590 prefixEnd_2052590 468429002938768651504585 := by
  unfold tailWord_2052590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358013454228057413505403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49909405089216306205362149 9358013454228057413505403)
  ·
    refine ⟨14037020181342086120258105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9358013454228057413505403 14037020181342086120258105)
    ·
      refine ⟨10527765136006564590193579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14037020181342086120258105 10527765136006564590193579)
      ·
        refine ⟨15791647704009846885290369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10527765136006564590193579 15791647704009846885290369)
        ·
          refine ⟨11843735778007385163967777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15791647704009846885290369 11843735778007385163967777)
          ·
            refine ⟨8882801833505538872975833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11843735778007385163967777 8882801833505538872975833)
            ·
              refine ⟨6662101375129154154731875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882801833505538872975833 6662101375129154154731875)
              ·
                refine ⟨9993152062693731232097813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662101375129154154731875 9993152062693731232097813)
                ·
                  refine ⟨468429002938768651504585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9993152062693731232097813 468429002938768651504585)
                  ·
                    rfl

theorem cell21_2052590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_2052590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052590 prefixEnd_2052590 := by exact prefixLift 2052590
  have htrace : WordTrace (prefixWord ++ tailWord_2052590) baseStart_2052590 baseEnd_2052590 := by
    simpa [prefixWord, tailWord_2052590, baseEnd_2052590] using wordTrace_append hprefix tailTrace_2052590
  have hstable : (prefixWord ++ tailWord_2052590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052590).length < 2 ^ (prefixWord ++ tailWord_2052590).sum := by decide
  have hdescent : baseEnd_2052590 < baseStart_2052590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052593 : List Nat := [1, 2, 2, 2, 3, 1, 5, 2, 3]
def baseStart_2052593 : Nat := 118140960795 + 2052593 * 2 ^ 59
def prefixEnd_2052593 : Nat := 4983230072969 + 3 ^ 40 * 2052593 * 2
def baseEnd_2052593 : Nat := 468429687579641312954579

theorem tailTrace_2052593 : CollatzResearch.WordTrace tailWord_2052593 prefixEnd_2052593 468429687579641312954579 := by
  unfold tailWord_2052593
  simp only [CollatzResearch.WordTrace]
  refine ⟨74864217052813590820402433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49909478035209060546934955 74864217052813590820402433)
  ·
    refine ⟨56148162789610193115301825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74864217052813590820402433 56148162789610193115301825)
    ·
      refine ⟨42111122092207644836476369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56148162789610193115301825 42111122092207644836476369)
      ·
        refine ⟨31583341569155733627357277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42111122092207644836476369 31583341569155733627357277)
        ·
          refine ⟨11843753088433400110258979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31583341569155733627357277 11843753088433400110258979)
          ·
            refine ⟨17765629632650100165388469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11843753088433400110258979 17765629632650100165388469)
            ·
              refine ⟨1665527778060946890505169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17765629632650100165388469 1665527778060946890505169)
              ·
                refine ⟨1249145833545710167878877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665527778060946890505169 1249145833545710167878877)
                ·
                  refine ⟨468429687579641312954579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249145833545710167878877 468429687579641312954579)
                  ·
                    rfl

theorem cell21_2052593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_2052593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052593 prefixEnd_2052593 := by exact prefixLift 2052593
  have htrace : WordTrace (prefixWord ++ tailWord_2052593) baseStart_2052593 baseEnd_2052593 := by
    simpa [prefixWord, tailWord_2052593, baseEnd_2052593] using wordTrace_append hprefix tailTrace_2052593
  have hstable : (prefixWord ++ tailWord_2052593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052593).length < 2 ^ (prefixWord ++ tailWord_2052593).sum := by decide
  have hdescent : baseEnd_2052593 < baseStart_2052593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052644 : List Nat := [2, 3, 1, 5, 2, 1, 2, 2, 3]
def baseStart_2052644 : Nat := 118140960795 + 2052644 * 2 ^ 59
def prefixEnd_2052644 : Nat := 4983230072969 + 3 ^ 40 * 2052644 * 2
def baseEnd_2052644 : Nat := 468441326474476557604475

theorem tailTrace_2052644 : CollatzResearch.WordTrace tailWord_2052644 prefixEnd_2052644 468441326474476557604475 := by
  unfold tailWord_2052644
  simp only [CollatzResearch.WordTrace]
  refine ⟨37433038587814413265254493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49910718117085884353672657 37433038587814413265254493)
  ·
    refine ⟨14037389470430404974470435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37433038587814413265254493 14037389470430404974470435)
    ·
      refine ⟨21056084205645607461705653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14037389470430404974470435 21056084205645607461705653)
      ·
        refine ⟨1974007894279275699534905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21056084205645607461705653 1974007894279275699534905)
        ·
          refine ⟨1480505920709456774651179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974007894279275699534905 1480505920709456774651179)
          ·
            refine ⟨2220758881064185161976769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480505920709456774651179 2220758881064185161976769)
            ·
              refine ⟨1665569160798138871482577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2220758881064185161976769 1665569160798138871482577)
              ·
                refine ⟨1249176870598604153611933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665569160798138871482577 1249176870598604153611933)
                ·
                  refine ⟨468441326474476557604475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249176870598604153611933 468441326474476557604475)
                  ·
                    rfl

theorem cell21_2052644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_2052644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052644 prefixEnd_2052644 := by exact prefixLift 2052644
  have htrace : WordTrace (prefixWord ++ tailWord_2052644) baseStart_2052644 baseEnd_2052644 := by
    simpa [prefixWord, tailWord_2052644, baseEnd_2052644] using wordTrace_append hprefix tailTrace_2052644
  have hstable : (prefixWord ++ tailWord_2052644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052644).length < 2 ^ (prefixWord ++ tailWord_2052644).sum := by decide
  have hdescent : baseEnd_2052644 < baseStart_2052644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052666 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_2052666 : Nat := 118140960795 + 2052666 * 2 ^ 59
def prefixEnd_2052666 : Nat := 4983230072969 + 3 ^ 40 * 2052666 * 2
def baseEnd_2052666 : Nat := 468446347174209408237763

theorem tailTrace_2052666 : CollatzResearch.WordTrace tailWord_2052666 prefixEnd_2052666 468446347174209408237763 := by
  unfold tailWord_2052666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18716719895387281071952463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49911253054366082858539901 18716719895387281071952463)
  ·
    refine ⟨28075079843080921607928695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18716719895387281071952463 28075079843080921607928695)
    ·
      refine ⟨42112619764621382411893043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28075079843080921607928695 42112619764621382411893043)
      ·
        refine ⟨63168929646932073617839565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42112619764621382411893043 63168929646932073617839565)
        ·
          refine ⟨23688348617599527606689837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63168929646932073617839565 23688348617599527606689837)
          ·
            refine ⟨8883130731599822852508689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23688348617599527606689837 8883130731599822852508689)
            ·
              refine ⟨6662348048699867139381517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8883130731599822852508689 6662348048699867139381517)
              ·
                refine ⟨2498380518262450177268069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6662348048699867139381517 2498380518262450177268069)
                ·
                  refine ⟨468446347174209408237763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498380518262450177268069 468446347174209408237763)
                  ·
                    rfl

theorem cell21_2052666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_2052666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052666 prefixEnd_2052666 := by exact prefixLift 2052666
  have htrace : WordTrace (prefixWord ++ tailWord_2052666) baseStart_2052666 baseEnd_2052666 := by
    simpa [prefixWord, tailWord_2052666, baseEnd_2052666] using wordTrace_append hprefix tailTrace_2052666
  have hstable : (prefixWord ++ tailWord_2052666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052666).length < 2 ^ (prefixWord ++ tailWord_2052666).sum := by decide
  have hdescent : baseEnd_2052666 < baseStart_2052666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052700 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_2052700 : Nat := 118140960795 + 2052700 * 2 ^ 59
def prefixEnd_2052700 : Nat := 4983230072969 + 3 ^ 40 * 2052700 * 2
def baseEnd_2052700 : Nat := 468454106437432904671027

theorem tailTrace_2052700 : CollatzResearch.WordTrace tailWord_2052700 prefixEnd_2052700 468454106437432904671027 := by
  unfold tailWord_2052700
  simp only [CollatzResearch.WordTrace]
  refine ⟨37434059831712974047273777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49912079775617298729698369 37434059831712974047273777)
  ·
    refine ⟨28075544873784730535455333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37434059831712974047273777 28075544873784730535455333)
    ·
      refine ⟨5264164663834636975397875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28075544873784730535455333 5264164663834636975397875)
      ·
        refine ⟨7896246995751955463096813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5264164663834636975397875 7896246995751955463096813)
        ·
          refine ⟨2961092623406983298661305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7896246995751955463096813 2961092623406983298661305)
          ·
            refine ⟨2220819467555237473995979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961092623406983298661305 2220819467555237473995979)
            ·
              refine ⟨3331229201332856210993969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220819467555237473995979 3331229201332856210993969)
              ·
                refine ⟨2498421900999642158245477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3331229201332856210993969 2498421900999642158245477)
                ·
                  refine ⟨468454106437432904671027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498421900999642158245477 468454106437432904671027)
                  ·
                    rfl

theorem cell21_2052700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_2052700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052700 prefixEnd_2052700 := by exact prefixLift 2052700
  have htrace : WordTrace (prefixWord ++ tailWord_2052700) baseStart_2052700 baseEnd_2052700 := by
    simpa [prefixWord, tailWord_2052700, baseEnd_2052700] using wordTrace_append hprefix tailTrace_2052700
  have hstable : (prefixWord ++ tailWord_2052700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052700).length < 2 ^ (prefixWord ++ tailWord_2052700).sum := by decide
  have hdescent : baseEnd_2052700 < baseStart_2052700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052762 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_2052762 : Nat := 118140960795 + 2052762 * 2 ^ 59
def prefixEnd_2052762 : Nat := 4983230072969 + 3 ^ 40 * 2052762 * 2
def baseEnd_2052762 : Nat := 468468255682134574637567

theorem tailTrace_2052762 : CollatzResearch.WordTrace tailWord_2052762 prefixEnd_2052762 468468255682134574637567 := by
  unfold tailWord_2052762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18717595247300333170826135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49913587326134221788869693 18717595247300333170826135)
  ·
    refine ⟨28076392870950499756239203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18717595247300333170826135 28076392870950499756239203)
    ·
      refine ⟨42114589306425749634358805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28076392870950499756239203 42114589306425749634358805)
      ·
        refine ⟨1974121373738707014110569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42114589306425749634358805 1974121373738707014110569)
        ·
          refine ⟨1480591030304030260582927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974121373738707014110569 1480591030304030260582927)
          ·
            refine ⟨2220886545456045390874391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480591030304030260582927 2220886545456045390874391)
            ·
              refine ⟨3331329818184068086311587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2220886545456045390874391 3331329818184068086311587)
              ·
                refine ⟨4996994727276102129467381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331329818184068086311587 4996994727276102129467381)
                ·
                  refine ⟨468468255682134574637567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4996994727276102129467381 468468255682134574637567)
                  ·
                    rfl

theorem cell21_2052762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_2052762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052762 prefixEnd_2052762 := by exact prefixLift 2052762
  have htrace : WordTrace (prefixWord ++ tailWord_2052762) baseStart_2052762 baseEnd_2052762 := by
    simpa [prefixWord, tailWord_2052762, baseEnd_2052762] using wordTrace_append hprefix tailTrace_2052762
  have hstable : (prefixWord ++ tailWord_2052762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052762).length < 2 ^ (prefixWord ++ tailWord_2052762).sum := by decide
  have hdescent : baseEnd_2052762 < baseStart_2052762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052925 : List Nat := [1, 4, 1, 4, 2, 2, 7]
def baseStart_2052925 : Nat := 118140960795 + 2052925 * 2 ^ 59
def prefixEnd_2052925 : Nat := 4983230072969 + 3 ^ 40 * 2052925 * 2
def baseEnd_2052925 : Nat := 52056161611431390380063

theorem tailTrace_2052925 : CollatzResearch.WordTrace tailWord_2052925 prefixEnd_2052925 52056161611431390380063 := by
  unfold tailWord_2052925
  simp only [CollatzResearch.WordTrace]
  refine ⟨74876326087610811521488229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49917550725073874347658819 74876326087610811521488229)
  ·
    refine ⟨14039311141427027160279043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74876326087610811521488229 14039311141427027160279043)
    ·
      refine ⟨21058966712140540740418565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14039311141427027160279043 21058966712140540740418565)
      ·
        refine ⟨3948556258526351388828481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21058966712140540740418565 3948556258526351388828481)
        ·
          refine ⟨2961417193894763541621361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3948556258526351388828481 2961417193894763541621361)
          ·
            refine ⟨2221062895421072656216021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2961417193894763541621361 2221062895421072656216021)
            ·
              refine ⟨52056161611431390380063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2221062895421072656216021 52056161611431390380063)
              ·
                rfl

theorem cell21_2052925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 7].length) (baseStart_2052925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052925 prefixEnd_2052925 := by exact prefixLift 2052925
  have htrace : WordTrace (prefixWord ++ tailWord_2052925) baseStart_2052925 baseEnd_2052925 := by
    simpa [prefixWord, tailWord_2052925, baseEnd_2052925] using wordTrace_append hprefix tailTrace_2052925
  have hstable : (prefixWord ++ tailWord_2052925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052925).length < 2 ^ (prefixWord ++ tailWord_2052925).sum := by decide
  have hdescent : baseEnd_2052925 < baseStart_2052925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2052990 : List Nat := [4, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2052990 : Nat := 118140960795 + 2052990 * 2 ^ 59
def prefixEnd_2052990 : Nat := 4983230072969 + 3 ^ 40 * 2052990 * 2
def baseEnd_2052990 : Nat := 468520288388456844837101

theorem tailTrace_2052990 : CollatzResearch.WordTrace tailWord_2052990 prefixEnd_2052990 468520288388456844837101 := by
  unfold tailWord_2052990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9359837104046915952825553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49919131221583551748402949 9359837104046915952825553)
  ·
    refine ⟨7019877828035186964619165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9359837104046915952825553 7019877828035186964619165)
    ·
      refine ⟨2632454185513195111732187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7019877828035186964619165 2632454185513195111732187)
      ·
        refine ⟨3948681278269792667598281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632454185513195111732187 3948681278269792667598281)
        ·
          refine ⟨2961510958702344500698711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3948681278269792667598281 2961510958702344500698711)
          ·
            refine ⟨4442266438053516751048067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961510958702344500698711 4442266438053516751048067)
            ·
              refine ⟨6663399657080275126572101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442266438053516751048067 6663399657080275126572101)
              ·
                refine ⟨1249387435702551586232269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6663399657080275126572101 1249387435702551586232269)
                ·
                  refine ⟨468520288388456844837101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249387435702551586232269 468520288388456844837101)
                  ·
                    rfl

theorem cell21_2052990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2052990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2052990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2052990 prefixEnd_2052990 := by exact prefixLift 2052990
  have htrace : WordTrace (prefixWord ++ tailWord_2052990) baseStart_2052990 baseEnd_2052990 := by
    simpa [prefixWord, tailWord_2052990, baseEnd_2052990] using wordTrace_append hprefix tailTrace_2052990
  have hstable : (prefixWord ++ tailWord_2052990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2052990).length < 2 ^ (prefixWord ++ tailWord_2052990).sum := by decide
  have hdescent : baseEnd_2052990 < baseStart_2052990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2052990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053069 : List Nat := [1, 6, 3, 1, 2, 1, 2, 5]
def baseStart_2053069 : Nat := 118140960795 + 2053069 * 2 ^ 59
def prefixEnd_2053069 : Nat := 4983230072969 + 3 ^ 40 * 2053069 * 2
def baseEnd_2053069 : Nat := 156179439088256754340091

theorem tailTrace_2053069 : CollatzResearch.WordTrace tailWord_2053069 prefixEnd_2053069 156179439088256754340091 := by
  unfold tailWord_2053069
  simp only [CollatzResearch.WordTrace]
  refine ⟨74881578199089124114730261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49921052132726082743153507 74881578199089124114730261)
  ·
    refine ⟨3510073978082302692877981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74881578199089124114730261 3510073978082302692877981)
    ·
      refine ⟨1316277741780863509829243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3510073978082302692877981 1316277741780863509829243)
      ·
        refine ⟨1974416612671295264743865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316277741780863509829243 1974416612671295264743865)
        ·
          refine ⟨1480812459503471448557899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974416612671295264743865 1480812459503471448557899)
          ·
            refine ⟨2221218689255207172836849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480812459503471448557899 2221218689255207172836849)
            ·
              refine ⟨1665914016941405379627637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2221218689255207172836849 1665914016941405379627637)
              ·
                refine ⟨156179439088256754340091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1665914016941405379627637 156179439088256754340091)
                ·
                  rfl

theorem cell21_2053069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 5].length) (baseStart_2053069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053069 prefixEnd_2053069 := by exact prefixLift 2053069
  have htrace : WordTrace (prefixWord ++ tailWord_2053069) baseStart_2053069 baseEnd_2053069 := by
    simpa [prefixWord, tailWord_2053069, baseEnd_2053069] using wordTrace_append hprefix tailTrace_2053069
  have hstable : (prefixWord ++ tailWord_2053069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053069).length < 2 ^ (prefixWord ++ tailWord_2053069).sum := by decide
  have hdescent : baseEnd_2053069 < baseStart_2053069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053105 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 6]
def baseStart_2053105 : Nat := 118140960795 + 2053105 * 2 ^ 59
def prefixEnd_2053105 : Nat := 4983230072969 + 3 ^ 40 * 2053105 * 2
def baseEnd_2053105 : Nat := 468546532955242200420199

theorem tailTrace_2053105 : CollatzResearch.WordTrace tailWord_2053105 prefixEnd_2053105 468546532955242200420199 := by
  unfold tailWord_2053105
  simp only [CollatzResearch.WordTrace]
  refine ⟨74882891226958702263040769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49921927484639134842027179 74882891226958702263040769)
  ·
    refine ⟨56162168420219026697280577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74882891226958702263040769 56162168420219026697280577)
    ·
      refine ⟨42121626315164270022960433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56162168420219026697280577 42121626315164270022960433)
      ·
        refine ⟨31591219736373202517220325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42121626315164270022960433 31591219736373202517220325)
        ·
          refine ⟨5923353700569975471978811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31591219736373202517220325 5923353700569975471978811)
          ·
            refine ⟨8885030550854963207968217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923353700569975471978811 8885030550854963207968217)
            ·
              refine ⟨6663772913141222405976163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8885030550854963207968217 6663772913141222405976163)
              ·
                refine ⟨9995659369711833608964245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663772913141222405976163 9995659369711833608964245)
                ·
                  refine ⟨468546532955242200420199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9995659369711833608964245 468546532955242200420199)
                  ·
                    rfl

theorem cell21_2053105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_2053105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053105 prefixEnd_2053105 := by exact prefixLift 2053105
  have htrace : WordTrace (prefixWord ++ tailWord_2053105) baseStart_2053105 baseEnd_2053105 := by
    simpa [prefixWord, tailWord_2053105, baseEnd_2053105] using wordTrace_append hprefix tailTrace_2053105
  have hstable : (prefixWord ++ tailWord_2053105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053105).length < 2 ^ (prefixWord ++ tailWord_2053105).sum := by decide
  have hdescent : baseEnd_2053105 < baseStart_2053105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053271 : List Nat := [1, 1, 3, 3, 3, 1, 9]
def baseStart_2053271 : Nat := 118140960795 + 2053271 * 2 ^ 59
def prefixEnd_2053271 : Nat := 4983230072969 + 3 ^ 40 * 2053271 * 2
def baseEnd_2053271 : Nat := 52064935157429200072577

theorem tailTrace_2053271 : CollatzResearch.WordTrace tailWord_2053271 prefixEnd_2053271 52064935157429200072577 := by
  unfold tailWord_2053271
  simp only [CollatzResearch.WordTrace]
  refine ⟨74888945744357312613583667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49925963829571541742389111 74888945744357312613583667)
  ·
    refine ⟨112333418616535968920375501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74888945744357312613583667 112333418616535968920375501)
    ·
      refine ⟨42125031981200988345140813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112333418616535968920375501 42125031981200988345140813)
      ·
        refine ⟨15796886992950370629427805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42125031981200988345140813 15796886992950370629427805)
        ·
          refine ⟨5923832622356388986035427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15796886992950370629427805 5923832622356388986035427)
          ·
            refine ⟨8885748933534583479053141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923832622356388986035427 8885748933534583479053141)
            ·
              refine ⟨52064935157429200072577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8885748933534583479053141 52064935157429200072577)
              ·
                rfl

theorem cell21_2053271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 9].length) (baseStart_2053271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053271 prefixEnd_2053271 := by exact prefixLift 2053271
  have htrace : WordTrace (prefixWord ++ tailWord_2053271) baseStart_2053271 baseEnd_2053271 := by
    simpa [prefixWord, tailWord_2053271, baseEnd_2053271] using wordTrace_append hprefix tailTrace_2053271
  have hstable : (prefixWord ++ tailWord_2053271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053271).length < 2 ^ (prefixWord ++ tailWord_2053271).sum := by decide
  have hdescent : baseEnd_2053271 < baseStart_2053271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053336 : List Nat := [2, 1, 2, 2, 5, 1, 1, 4, 3]
def baseStart_2053336 : Nat := 118140960795 + 2053336 * 2 ^ 59
def prefixEnd_2053336 : Nat := 4983230072969 + 3 ^ 40 * 2053336 * 2
def baseEnd_2053336 : Nat := 468599250302437132069727

theorem tailTrace_2053336 : CollatzResearch.WordTrace tailWord_2053336 prefixEnd_2053336 468599250302437132069727 := by
  unfold tailWord_2053336
  simp only [CollatzResearch.WordTrace]
  refine ⟨37445658244560914357349931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49927544326081219143133241 37445658244560914357349931)
  ·
    refine ⟨56168487366841371536024897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37445658244560914357349931 56168487366841371536024897)
    ·
      refine ⟨42126365525131028652018673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56168487366841371536024897 42126365525131028652018673)
      ·
        refine ⟨31594774143848271489014005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42126365525131028652018673 31594774143848271489014005)
        ·
          refine ⟨2962010075985775452095063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31594774143848271489014005 2962010075985775452095063)
          ·
            refine ⟨4443015113978663178142595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962010075985775452095063 4443015113978663178142595)
            ·
              refine ⟨6664522670967994767213893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443015113978663178142595 6664522670967994767213893)
              ·
                refine ⟨1249598000806499018852605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6664522670967994767213893 1249598000806499018852605)
                ·
                  refine ⟨468599250302437132069727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249598000806499018852605 468599250302437132069727)
                  ·
                    rfl

theorem cell21_2053336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_2053336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053336 prefixEnd_2053336 := by exact prefixLift 2053336
  have htrace : WordTrace (prefixWord ++ tailWord_2053336) baseStart_2053336 baseEnd_2053336 := by
    simpa [prefixWord, tailWord_2053336, baseEnd_2053336] using wordTrace_append hprefix tailTrace_2053336
  have hstable : (prefixWord ++ tailWord_2053336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053336).length < 2 ^ (prefixWord ++ tailWord_2053336).sum := by decide
  have hdescent : baseEnd_2053336 < baseStart_2053336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053446 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2053446 : Nat := 118140960795 + 2053446 * 2 ^ 59
def prefixEnd_2053446 : Nat := 4983230072969 + 3 ^ 40 * 2053446 * 2
def baseEnd_2053446 : Nat := 468624353801101385236169

theorem tailTrace_2053446 : CollatzResearch.WordTrace tailWord_2053446 prefixEnd_2053446 468624353801101385236169 := by
  unfold tailWord_2053446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340479016210103671912631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49930219012482211667469461 2340479016210103671912631)
  ·
    refine ⟨3510718524315155507868947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2340479016210103671912631 3510718524315155507868947)
    ·
      refine ⟨5266077786472733261803421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3510718524315155507868947 5266077786472733261803421)
      ·
        refine ⟨1974779169927274973176283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5266077786472733261803421 1974779169927274973176283)
        ·
          refine ⟨2962168754890912459764425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974779169927274973176283 2962168754890912459764425)
          ·
            refine ⟨2221626566168184344823319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2962168754890912459764425 2221626566168184344823319)
            ·
              refine ⟨3332439849252276517234979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221626566168184344823319 3332439849252276517234979)
              ·
                refine ⟨4998659773878414775852469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332439849252276517234979 4998659773878414775852469)
                ·
                  refine ⟨468624353801101385236169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4998659773878414775852469 468624353801101385236169)
                  ·
                    rfl

theorem cell21_2053446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2053446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053446 prefixEnd_2053446 := by exact prefixLift 2053446
  have htrace : WordTrace (prefixWord ++ tailWord_2053446) baseStart_2053446 baseEnd_2053446 := by
    simpa [prefixWord, tailWord_2053446, baseEnd_2053446] using wordTrace_append hprefix tailTrace_2053446
  have hstable : (prefixWord ++ tailWord_2053446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053446).length < 2 ^ (prefixWord ++ tailWord_2053446).sum := by decide
  have hdescent : baseEnd_2053446 < baseStart_2053446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053530 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_2053530 : Nat := 118140960795 + 2053530 * 2 ^ 59
def prefixEnd_2053530 : Nat := 4983230072969 + 3 ^ 40 * 2053530 * 2
def baseEnd_2053530 : Nat := 468643523745535905835997

theorem tailTrace_2053530 : CollatzResearch.WordTrace tailWord_2053530 prefixEnd_2053530 468643523745535905835997 := by
  unfold tailWord_2053530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18724598062604749961815511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49932261500279333231508029 18724598062604749961815511)
  ·
    refine ⟨28086897093907124942723267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18724598062604749961815511 28086897093907124942723267)
    ·
      refine ⟨42130345640860687414084901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28086897093907124942723267 42130345640860687414084901)
      ·
        refine ⟨7899439807661378890140919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42130345640860687414084901 7899439807661378890140919)
        ·
          refine ⟨11849159711492068335211379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7899439807661378890140919 11849159711492068335211379)
          ·
            refine ⟨17773739567238102502817069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11849159711492068335211379 17773739567238102502817069)
            ·
              refine ⟨6665152337714288438556401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17773739567238102502817069 6665152337714288438556401)
              ·
                refine ⟨4998864253285716328917301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6665152337714288438556401 4998864253285716328917301)
                ·
                  refine ⟨468643523745535905835997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4998864253285716328917301 468643523745535905835997)
                  ·
                    rfl

theorem cell21_2053530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_2053530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053530 prefixEnd_2053530 := by exact prefixLift 2053530
  have htrace : WordTrace (prefixWord ++ tailWord_2053530) baseStart_2053530 baseEnd_2053530 := by
    simpa [prefixWord, tailWord_2053530, baseEnd_2053530] using wordTrace_append hprefix tailTrace_2053530
  have hstable : (prefixWord ++ tailWord_2053530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053530).length < 2 ^ (prefixWord ++ tailWord_2053530).sum := by decide
  have hdescent : baseEnd_2053530 < baseStart_2053530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053561 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 6]
def baseStart_2053561 : Nat := 118140960795 + 2053561 * 2 ^ 59
def prefixEnd_2053561 : Nat := 4983230072969 + 3 ^ 40 * 2053561 * 2
def baseEnd_2053561 : Nat := 468650598367886740819267

theorem tailTrace_2053561 : CollatzResearch.WordTrace tailWord_2053561 prefixEnd_2053561 468650598367886740819267 := by
  unfold tailWord_2053561
  simp only [CollatzResearch.WordTrace]
  refine ⟨74899522913306692141640537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49933015275537794761093691 74899522913306692141640537)
  ·
    refine ⟨56174642184980019106230403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74899522913306692141640537 56174642184980019106230403)
    ·
      refine ⟨84261963277470028659345605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56174642184980019106230403 84261963277470028659345605)
      ·
        refine ⟨15799118114525630373627301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84261963277470028659345605 15799118114525630373627301)
        ·
          refine ⟨2962334646473555695055119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15799118114525630373627301 2962334646473555695055119)
          ·
            refine ⟨4443501969710333542582679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962334646473555695055119 4443501969710333542582679)
            ·
              refine ⟨6665252954565500313874019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443501969710333542582679 6665252954565500313874019)
              ·
                refine ⟨9997879431848250470811029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665252954565500313874019 9997879431848250470811029)
                ·
                  refine ⟨468650598367886740819267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9997879431848250470811029 468650598367886740819267)
                  ·
                    rfl

theorem cell21_2053561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_2053561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053561 prefixEnd_2053561 := by exact prefixLift 2053561
  have htrace : WordTrace (prefixWord ++ tailWord_2053561) baseStart_2053561 baseEnd_2053561 := by
    simpa [prefixWord, tailWord_2053561, baseEnd_2053561] using wordTrace_append hprefix tailTrace_2053561
  have hstable : (prefixWord ++ tailWord_2053561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053561).length < 2 ^ (prefixWord ++ tailWord_2053561).sum := by decide
  have hdescent : baseEnd_2053561 < baseStart_2053561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053570 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2053570 : Nat := 118140960795 + 2053570 * 2 ^ 59
def prefixEnd_2053570 : Nat := 4983230072969 + 3 ^ 40 * 2053570 * 2
def baseEnd_2053570 : Nat := 468652652290504725169249

theorem tailTrace_2053570 : CollatzResearch.WordTrace tailWord_2053570 prefixEnd_2053570 468652652290504725169249 := by
  unfold tailWord_2053570
  simp only [CollatzResearch.WordTrace]
  refine ⟨18724962792568521669679541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49933234113516057785812109 18724962792568521669679541)
  ·
    refine ⟨1755465261803298906532457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18724962792568521669679541 1755465261803298906532457)
    ·
      refine ⟨1316598946352474179899343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1755465261803298906532457 1316598946352474179899343)
      ·
        refine ⟨1974898419528711269849015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316598946352474179899343 1974898419528711269849015)
        ·
          refine ⟨2962347629293066904773523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974898419528711269849015 2962347629293066904773523)
          ·
            refine ⟨4443521443939600357160285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962347629293066904773523 4443521443939600357160285)
            ·
              refine ⟨1666320541477350133935107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4443521443939600357160285 1666320541477350133935107)
              ·
                refine ⟨2499480812216025200902661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666320541477350133935107 2499480812216025200902661)
                ·
                  refine ⟨468652652290504725169249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2499480812216025200902661 468652652290504725169249)
                  ·
                    rfl

theorem cell21_2053570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2053570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053570 prefixEnd_2053570 := by exact prefixLift 2053570
  have htrace : WordTrace (prefixWord ++ tailWord_2053570) baseStart_2053570 baseEnd_2053570 := by
    simpa [prefixWord, tailWord_2053570, baseEnd_2053570] using wordTrace_append hprefix tailTrace_2053570
  have hstable : (prefixWord ++ tailWord_2053570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053570).length < 2 ^ (prefixWord ++ tailWord_2053570).sum := by decide
  have hdescent : baseEnd_2053570 < baseStart_2053570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053578 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_2053578 : Nat := 118140960795 + 2053578 * 2 ^ 59
def prefixEnd_2053578 : Nat := 4983230072969 + 3 ^ 40 * 2053578 * 2
def baseEnd_2053578 : Nat := 468654477999498489035899

theorem tailTrace_2053578 : CollatzResearch.WordTrace tailWord_2053578 prefixEnd_2053578 468654477999498489035899 := by
  unfold tailWord_2053578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725035738561276011252347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49933428636163402696672925 18725035738561276011252347)
  ·
    refine ⟨28087553607841914016878521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18725035738561276011252347 28087553607841914016878521)
    ·
      refine ⟨21065665205881435512658891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28087553607841914016878521 21065665205881435512658891)
      ·
        refine ⟨31598497808822153268988337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21065665205881435512658891 31598497808822153268988337)
        ·
          refine ⟨23698873356616614951741253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31598497808822153268988337 23698873356616614951741253)
          ·
            refine ⟨4443538754365615303451485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23698873356616614951741253 4443538754365615303451485)
            ·
              refine ⟨1666327032887105738794307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4443538754365615303451485 1666327032887105738794307)
              ·
                refine ⟨2499490549330658608191461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666327032887105738794307 2499490549330658608191461)
                ·
                  refine ⟨468654477999498489035899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2499490549330658608191461 468654477999498489035899)
                  ·
                    rfl

theorem cell21_2053578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_2053578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053578 prefixEnd_2053578 := by exact prefixLift 2053578
  have htrace : WordTrace (prefixWord ++ tailWord_2053578) baseStart_2053578 baseEnd_2053578 := by
    simpa [prefixWord, tailWord_2053578, baseEnd_2053578] using wordTrace_append hprefix tailTrace_2053578
  have hstable : (prefixWord ++ tailWord_2053578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053578).length < 2 ^ (prefixWord ++ tailWord_2053578).sum := by decide
  have hdescent : baseEnd_2053578 < baseStart_2053578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053702 : List Nat := [6, 1, 1, 1, 3, 1, 3, 5]
def baseStart_2053702 : Nat := 118140960795 + 2053702 * 2 ^ 59
def prefixEnd_2053702 : Nat := 4983230072969 + 3 ^ 40 * 2053702 * 2
def baseEnd_2053702 : Nat := 156227592162967276322993

theorem tailTrace_2053702 : CollatzResearch.WordTrace tailWord_2053702 prefixEnd_2053702 156227592162967276322993 := by
  unfold tailWord_2053702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2340770800181121038203855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49936443737197248815015573 2340770800181121038203855)
  ·
    refine ⟨3511156200271681557305783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2340770800181121038203855 3511156200271681557305783)
    ·
      refine ⟨5266734300407522335958675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511156200271681557305783 5266734300407522335958675)
      ·
        refine ⟨7900101450611283503938013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266734300407522335958675 7900101450611283503938013)
        ·
          refine ⟨2962538043979231313976755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7900101450611283503938013 2962538043979231313976755)
          ·
            refine ⟨4443807065968846970965133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962538043979231313976755 4443807065968846970965133)
            ·
              refine ⟨1666427649738317614111925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4443807065968846970965133 1666427649738317614111925)
              ·
                refine ⟨156227592162967276322993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1666427649738317614111925 156227592162967276322993)
                ·
                  rfl

theorem cell21_2053702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_2053702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053702 prefixEnd_2053702 := by exact prefixLift 2053702
  have htrace : WordTrace (prefixWord ++ tailWord_2053702) baseStart_2053702 baseEnd_2053702 := by
    simpa [prefixWord, tailWord_2053702, baseEnd_2053702] using wordTrace_append hprefix tailTrace_2053702
  have hstable : (prefixWord ++ tailWord_2053702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053702).length < 2 ^ (prefixWord ++ tailWord_2053702).sum := by decide
  have hdescent : baseEnd_2053702 < baseStart_2053702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053792 : List Nat := [2, 1, 1, 4, 3, 2, 3, 2, 3]
def baseStart_2053792 : Nat := 118140960795 + 2053792 * 2 ^ 59
def prefixEnd_2053792 : Nat := 4983230072969 + 3 ^ 40 * 2053792 * 2
def baseEnd_2053792 : Nat := 468703315715081672468795

theorem tailTrace_2053792 : CollatzResearch.WordTrace tailWord_2053792 prefixEnd_2053792 468703315715081672468795 := by
  unfold tailWord_2053792
  simp only [CollatzResearch.WordTrace]
  refine ⟨37453974087734909296649815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49938632116979879062199753 37453974087734909296649815)
  ·
    refine ⟨56180961131602363944974723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37453974087734909296649815 56180961131602363944974723)
    ·
      refine ⟨84271441697403545917462085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56180961131602363944974723 84271441697403545917462085)
      ·
        refine ⟨15800895318263164859524141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84271441697403545917462085 15800895318263164859524141)
        ·
          refine ⟨5925335744348686822321553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15800895318263164859524141 5925335744348686822321553)
          ·
            refine ⟨4444001808261515116741165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5925335744348686822321553 4444001808261515116741165)
            ·
              refine ⟨1666500678098068168777937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4444001808261515116741165 1666500678098068168777937)
              ·
                refine ⟨1249875508573551126583453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1666500678098068168777937 1249875508573551126583453)
                ·
                  refine ⟨468703315715081672468795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249875508573551126583453 468703315715081672468795)
                  ·
                    rfl

theorem cell21_2053792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_2053792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053792 prefixEnd_2053792 := by exact prefixLift 2053792
  have htrace : WordTrace (prefixWord ++ tailWord_2053792) baseStart_2053792 baseEnd_2053792 := by
    simpa [prefixWord, tailWord_2053792, baseEnd_2053792] using wordTrace_append hprefix tailTrace_2053792
  have hstable : (prefixWord ++ tailWord_2053792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053792).length < 2 ^ (prefixWord ++ tailWord_2053792).sum := by decide
  have hdescent : baseEnd_2053792 < baseStart_2053792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053817 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 5]
def baseStart_2053817 : Nat := 118140960795 + 2053817 * 2 ^ 59
def prefixEnd_2053817 : Nat := 4983230072969 + 3 ^ 40 * 2053817 * 2
def baseEnd_2053817 : Nat := 468709021055687184552077

theorem tailTrace_2053817 : CollatzResearch.WordTrace tailWord_2053817 prefixEnd_2053817 468709021055687184552077 := by
  unfold tailWord_2053817
  simp only [CollatzResearch.WordTrace]
  refine ⟨74908860000379247862959705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49939240000252831908639803 74908860000379247862959705)
  ·
    refine ⟨56181645000284435897219779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74908860000379247862959705 56181645000284435897219779)
    ·
      refine ⟨84272467500426653845829669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56181645000284435897219779 84272467500426653845829669)
      ·
        refine ⟨15801087656329997596093063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84272467500426653845829669 15801087656329997596093063)
        ·
          refine ⟨23701631484494996394139595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15801087656329997596093063 23701631484494996394139595)
          ·
            refine ⟨35552447226742494591209393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23701631484494996394139595 35552447226742494591209393)
            ·
              refine ⟨26664335420056870943407045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35552447226742494591209393 26664335420056870943407045)
              ·
                refine ⟨4999562891260663301888821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26664335420056870943407045 4999562891260663301888821)
                ·
                  refine ⟨468709021055687184552077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4999562891260663301888821 468709021055687184552077)
                  ·
                    rfl

theorem cell21_2053817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_2053817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053817 prefixEnd_2053817 := by exact prefixLift 2053817
  have htrace : WordTrace (prefixWord ++ tailWord_2053817) baseStart_2053817 baseEnd_2053817 := by
    simpa [prefixWord, tailWord_2053817, baseEnd_2053817] using wordTrace_append hprefix tailTrace_2053817
  have hstable : (prefixWord ++ tailWord_2053817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053817).length < 2 ^ (prefixWord ++ tailWord_2053817).sum := by decide
  have hdescent : baseEnd_2053817 < baseStart_2053817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053958 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2053958 : Nat := 118140960795 + 2053958 * 2 ^ 59
def prefixEnd_2053958 : Nat := 4983230072969 + 3 ^ 40 * 2053958 * 2
def baseEnd_2053958 : Nat := 468741199176702272701789

theorem tailTrace_2053958 : CollatzResearch.WordTrace tailWord_2053958 prefixEnd_2053958 468741199176702272701789 := by
  unfold tailWord_2053958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341062584152138404495079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49942668461912285962561685 2341062584152138404495079)
  ·
    refine ⟨3511593876228207606742619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2341062584152138404495079 3511593876228207606742619)
    ·
      refine ⟨5267390814342311410113929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3511593876228207606742619 5267390814342311410113929)
      ·
        refine ⟨3950543110756733557585447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5267390814342311410113929 3950543110756733557585447)
        ·
          refine ⟨5925814666135100336378171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3950543110756733557585447 5925814666135100336378171)
          ·
            refine ⟨8888721999202650504567257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5925814666135100336378171 8888721999202650504567257)
            ·
              refine ⟨6666541499401987878425443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8888721999202650504567257 6666541499401987878425443)
              ·
                refine ⟨9999812249102981817638165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6666541499401987878425443 9999812249102981817638165)
                ·
                  refine ⟨468741199176702272701789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9999812249102981817638165 468741199176702272701789)
                  ·
                    rfl

theorem cell21_2053958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2053958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053958 prefixEnd_2053958 := by exact prefixLift 2053958
  have htrace : WordTrace (prefixWord ++ tailWord_2053958) baseStart_2053958 baseEnd_2053958 := by
    simpa [prefixWord, tailWord_2053958, baseEnd_2053958] using wordTrace_append hprefix tailTrace_2053958
  have hstable : (prefixWord ++ tailWord_2053958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053958).length < 2 ^ (prefixWord ++ tailWord_2053958).sum := by decide
  have hdescent : baseEnd_2053958 < baseStart_2053958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2053975 : List Nat := [1, 1, 3, 2, 6, 1, 2, 1, 4]
def baseStart_2053975 : Nat := 118140960795 + 2053975 * 2 ^ 59
def prefixEnd_2053975 : Nat := 4983230072969 + 3 ^ 40 * 2053975 * 2
def baseEnd_2053975 : Nat := 468745078808314020918421

theorem tailTrace_2053975 : CollatzResearch.WordTrace tailWord_2053975 prefixEnd_2053975 468745078808314020918421 := by
  unfold tailWord_2053975
  simp only [CollatzResearch.WordTrace]
  refine ⟨74914622733806840847211379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49943081822537893898140919 74914622733806840847211379)
  ·
    refine ⟨112371934100710261270817069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74914622733806840847211379 112371934100710261270817069)
    ·
      refine ⟨42139475287766347976556401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112371934100710261270817069 42139475287766347976556401)
      ·
        refine ⟨31604606465824760982417301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42139475287766347976556401 31604606465824760982417301)
        ·
          refine ⟨1481465928085535671050811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31604606465824760982417301 1481465928085535671050811)
          ·
            refine ⟨2222198892128303506576217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481465928085535671050811 2222198892128303506576217)
            ·
              refine ⟨1666649169096227629932163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222198892128303506576217 1666649169096227629932163)
              ·
                refine ⟨2499973753644341444898245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666649169096227629932163 2499973753644341444898245)
                ·
                  refine ⟨468745078808314020918421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2499973753644341444898245 468745078808314020918421)
                  ·
                    rfl

theorem cell21_2053975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 4].length) (baseStart_2053975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2053975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2053975 prefixEnd_2053975 := by exact prefixLift 2053975
  have htrace : WordTrace (prefixWord ++ tailWord_2053975) baseStart_2053975 baseEnd_2053975 := by
    simpa [prefixWord, tailWord_2053975, baseEnd_2053975] using wordTrace_append hprefix tailTrace_2053975
  have hstable : (prefixWord ++ tailWord_2053975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2053975).length < 2 ^ (prefixWord ++ tailWord_2053975).sum := by decide
  have hdescent : baseEnd_2053975 < baseStart_2053975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2053975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054045 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 7]
def baseStart_2054045 : Nat := 118140960795 + 2054045 * 2 ^ 59
def prefixEnd_2054045 : Nat := 4983230072969 + 3 ^ 40 * 2054045 * 2
def baseEnd_2054045 : Nat := 468761053762009454751611

theorem tailTrace_2054045 : CollatzResearch.WordTrace tailWord_2054045 prefixEnd_2054045 468761053762009454751611 := by
  unfold tailWord_2054045
  simp only [CollatzResearch.WordTrace]
  refine ⟨74917175843553242802259589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49944783895702161868173059 74917175843553242802259589)
  ·
    refine ⟨14046970470666233025423673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74917175843553242802259589 14046970470666233025423673)
    ·
      refine ⟨10535227852999674769067755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14046970470666233025423673 10535227852999674769067755)
      ·
        refine ⟨15802841779499512153601633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10535227852999674769067755 15802841779499512153601633)
        ·
          refine ⟨11852131334624634115201225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15802841779499512153601633 11852131334624634115201225)
          ·
            refine ⟨8889098500968475586400919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11852131334624634115201225 8889098500968475586400919)
            ·
              refine ⟨13333647751452713379601379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8889098500968475586400919 13333647751452713379601379)
              ·
                refine ⟨20000471627179070069402069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13333647751452713379601379 20000471627179070069402069)
                ·
                  refine ⟨468761053762009454751611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20000471627179070069402069 468761053762009454751611)
                  ·
                    rfl

theorem cell21_2054045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_2054045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054045 prefixEnd_2054045 := by exact prefixLift 2054045
  have htrace : WordTrace (prefixWord ++ tailWord_2054045) baseStart_2054045 baseEnd_2054045 := by
    simpa [prefixWord, tailWord_2054045, baseEnd_2054045] using wordTrace_append hprefix tailTrace_2054045
  have hstable : (prefixWord ++ tailWord_2054045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054045).length < 2 ^ (prefixWord ++ tailWord_2054045).sum := by decide
  have hdescent : baseEnd_2054045 < baseStart_2054045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054068 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 4]
def baseStart_2054068 : Nat := 118140960795 + 2054068 * 2 ^ 59
def prefixEnd_2054068 : Nat := 4983230072969 + 3 ^ 40 * 2054068 * 2
def baseEnd_2054068 : Nat := 468766302675366525868231

theorem tailTrace_2054068 : CollatzResearch.WordTrace tailWord_2054068 prefixEnd_2054068 468766302675366525868231 := by
  unfold tailWord_2054068
  simp only [CollatzResearch.WordTrace]
  refine ⟨37459007361234958865173429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49945343148313278486897905 37459007361234958865173429)
  ·
    refine ⟨3511781940115777393610009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37459007361234958865173429 3511781940115777393610009)
    ·
      refine ⟨2633836455086833045207507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3511781940115777393610009 2633836455086833045207507)
      ·
        refine ⟨3950754682630249567811261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2633836455086833045207507 3950754682630249567811261)
        ·
          refine ⟨1481533005986343587929223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3950754682630249567811261 1481533005986343587929223)
          ·
            refine ⟨2222299508979515381893835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481533005986343587929223 2222299508979515381893835)
            ·
              refine ⟨3333449263469273072840753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222299508979515381893835 3333449263469273072840753)
              ·
                refine ⟨2500086947601954804630565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333449263469273072840753 2500086947601954804630565)
                ·
                  refine ⟨468766302675366525868231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500086947601954804630565 468766302675366525868231)
                  ·
                    rfl

theorem cell21_2054068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_2054068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054068 prefixEnd_2054068 := by exact prefixLift 2054068
  have htrace : WordTrace (prefixWord ++ tailWord_2054068) baseStart_2054068 baseEnd_2054068 := by
    simpa [prefixWord, tailWord_2054068, baseEnd_2054068] using wordTrace_append hprefix tailTrace_2054068
  have hstable : (prefixWord ++ tailWord_2054068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054068).length < 2 ^ (prefixWord ++ tailWord_2054068).sum := by decide
  have hdescent : baseEnd_2054068 < baseStart_2054068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054152 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_2054152 : Nat := 118140960795 + 2054152 * 2 ^ 59
def prefixEnd_2054152 : Nat := 4983230072969 + 3 ^ 40 * 2054152 * 2
def baseEnd_2054152 : Nat := 468785472619801046468059

theorem tailTrace_2054152 : CollatzResearch.WordTrace tailWord_2054152 prefixEnd_2054152 468785472619801046468059 := by
  unfold tailWord_2054152
  simp only [CollatzResearch.WordTrace]
  refine ⟨37460539227082800038202355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49947385636110400050936473 37460539227082800038202355)
  ·
    refine ⟨56190808840624200057303533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37460539227082800038202355 56190808840624200057303533)
    ·
      refine ⟨21071553315234075021488825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56190808840624200057303533 21071553315234075021488825)
      ·
        refine ⟨15803664986425556266116619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21071553315234075021488825 15803664986425556266116619)
        ·
          refine ⟨23705497479638334399174929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15803664986425556266116619 23705497479638334399174929)
          ·
            refine ⟨17779123109728750799381197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23705497479638334399174929 17779123109728750799381197)
            ·
              refine ⟨6667171166148281549767949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17779123109728750799381197 6667171166148281549767949)
              ·
                refine ⟨2500189187305605581162981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6667171166148281549767949 2500189187305605581162981)
                ·
                  refine ⟨468785472619801046468059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500189187305605581162981 468785472619801046468059)
                  ·
                    rfl

theorem cell21_2054152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_2054152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054152 prefixEnd_2054152 := by exact prefixLift 2054152
  have htrace : WordTrace (prefixWord ++ tailWord_2054152) baseStart_2054152 baseEnd_2054152 := by
    simpa [prefixWord, tailWord_2054152, baseEnd_2054152] using wordTrace_append hprefix tailTrace_2054152
  have hstable : (prefixWord ++ tailWord_2054152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054152).length < 2 ^ (prefixWord ++ tailWord_2054152).sum := by decide
  have hdescent : baseEnd_2054152 < baseStart_2054152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054183 : List Nat := [1, 1, 7, 1, 2, 9]
def baseStart_2054183 : Nat := 118140960795 + 2054183 * 2 ^ 59
def prefixEnd_2054183 : Nat := 4983230072969 + 3 ^ 40 * 2054183 * 2
def baseEnd_2054183 : Nat := 17362686934894514127827

theorem tailTrace_2054183 : CollatzResearch.WordTrace tailWord_2054183 prefixEnd_2054183 17362686934894514127827 := by
  unfold tailWord_2054183
  simp only [CollatzResearch.WordTrace]
  refine ⟨74922209117053292370783203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49948139411368861580522135 74922209117053292370783203)
  ·
    refine ⟨112383313675579938556174805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74922209117053292370783203 112383313675579938556174805)
    ·
      refine ⟨2633983914271404809910347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 112383313675579938556174805 2633983914271404809910347)
      ·
        refine ⟨3950975871407107214865521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2633983914271404809910347 3950975871407107214865521)
        ·
          refine ⟨2963231903555330411149141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3950975871407107214865521 2963231903555330411149141)
          ·
            refine ⟨17362686934894514127827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2963231903555330411149141 17362686934894514127827)
            ·
              rfl

theorem cell21_2054183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 9].length) (baseStart_2054183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054183 prefixEnd_2054183 := by exact prefixLift 2054183
  have htrace : WordTrace (prefixWord ++ tailWord_2054183) baseStart_2054183 baseEnd_2054183 := by
    simpa [prefixWord, tailWord_2054183, baseEnd_2054183] using wordTrace_append hprefix tailTrace_2054183
  have hstable : (prefixWord ++ tailWord_2054183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054183).length < 2 ^ (prefixWord ++ tailWord_2054183).sum := by decide
  have hdescent : baseEnd_2054183 < baseStart_2054183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054200 : List Nat := [2, 1, 2, 1, 7, 1, 1, 6]
def baseStart_2054200 : Nat := 118140960795 + 2054200 * 2 ^ 59
def prefixEnd_2054200 : Nat := 4983230072969 + 3 ^ 40 * 2054200 * 2
def baseEnd_2054200 : Nat := 156265475624587876555987

theorem tailTrace_2054200 : CollatzResearch.WordTrace tailWord_2054200 prefixEnd_2054200 156265475624587876555987 := by
  unfold tailWord_2054200
  simp only [CollatzResearch.WordTrace]
  refine ⟨37461414578995852137076027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49948552771994469516101369 37461414578995852137076027)
  ·
    refine ⟨56192121868493778205614041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37461414578995852137076027 56192121868493778205614041)
    ·
      refine ⟨42144091401370333654210531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56192121868493778205614041 42144091401370333654210531)
      ·
        refine ⟨63216137102055500481315797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42144091401370333654210531 63216137102055500481315797)
        ·
          refine ⟨1481628213329425792530839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 63216137102055500481315797 1481628213329425792530839)
          ·
            refine ⟨2222442319994138688796259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1481628213329425792530839 2222442319994138688796259)
            ·
              refine ⟨3333663479991208033194389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222442319994138688796259 3333663479991208033194389)
              ·
                refine ⟨156265475624587876555987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3333663479991208033194389 156265475624587876555987)
                ·
                  rfl

theorem cell21_2054200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_2054200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054200 prefixEnd_2054200 := by exact prefixLift 2054200
  have htrace : WordTrace (prefixWord ++ tailWord_2054200) baseStart_2054200 baseEnd_2054200 := by
    simpa [prefixWord, tailWord_2054200, baseEnd_2054200] using wordTrace_append hprefix tailTrace_2054200
  have hstable : (prefixWord ++ tailWord_2054200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054200).length < 2 ^ (prefixWord ++ tailWord_2054200).sum := by decide
  have hdescent : baseEnd_2054200 < baseStart_2054200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054245 : List Nat := [1, 3, 1, 3, 2, 4, 1, 2, 4]
def baseStart_2054245 : Nat := 118140960795 + 2054245 * 2 ^ 59
def prefixEnd_2054245 : Nat := 4983230072969 + 3 ^ 40 * 2054245 * 2
def baseEnd_2054245 : Nat := 468806696486853551417869

theorem tailTrace_2054245 : CollatzResearch.WordTrace tailWord_2054245 prefixEnd_2054245 468806696486853551417869 := by
  unfold tailWord_2054245
  simp only [CollatzResearch.WordTrace]
  refine ⟨74924470442828676959540189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49949646961885784639693459 74924470442828676959540189)
  ·
    refine ⟨28096676416060753859827571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74924470442828676959540189 28096676416060753859827571)
    ·
      refine ⟨42145014624091130789741357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28096676416060753859827571 42145014624091130789741357)
      ·
        refine ⟨15804380484034174046153009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42145014624091130789741357 15804380484034174046153009)
        ·
          refine ⟨11853285363025630534614757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15804380484034174046153009 11853285363025630534614757)
          ·
            refine ⟨2222491005567305725240267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11853285363025630534614757 2222491005567305725240267)
            ·
              refine ⟨3333736508350958587860401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2222491005567305725240267 3333736508350958587860401)
              ·
                refine ⟨2500302381263218940895301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3333736508350958587860401 2500302381263218940895301)
                ·
                  refine ⟨468806696486853551417869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500302381263218940895301 468806696486853551417869)
                  ·
                    rfl

theorem cell21_2054245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_2054245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054245 prefixEnd_2054245 := by exact prefixLift 2054245
  have htrace : WordTrace (prefixWord ++ tailWord_2054245) baseStart_2054245 baseEnd_2054245 := by
    simpa [prefixWord, tailWord_2054245, baseEnd_2054245] using wordTrace_append hprefix tailTrace_2054245
  have hstable : (prefixWord ++ tailWord_2054245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054245).length < 2 ^ (prefixWord ++ tailWord_2054245).sum := by decide
  have hdescent : baseEnd_2054245 < baseStart_2054245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054262 : List Nat := [5, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_2054262 : Nat := 118140960795 + 2054262 * 2 ^ 59
def prefixEnd_2054262 : Nat := 4983230072969 + 3 ^ 40 * 2054262 * 2
def baseEnd_2054262 : Nat := 468810576118465299634501

theorem tailTrace_2054262 : CollatzResearch.WordTrace tailWord_2054262 prefixEnd_2054262 468810576118465299634501 := by
  unfold tailWord_2054262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4682818155235443053931815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49950060322511392575272693 4682818155235443053931815)
  ·
    refine ⟨7024227232853164580897723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4682818155235443053931815 7024227232853164580897723)
    ·
      refine ⟨10536340849279746871346585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7024227232853164580897723 10536340849279746871346585)
      ·
        refine ⟨7902255636959810153509939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10536340849279746871346585 7902255636959810153509939)
        ·
          refine ⟨11853383455439715230264909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7902255636959810153509939 11853383455439715230264909)
          ·
            refine ⟨4445018795789893211349341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11853383455439715230264909 4445018795789893211349341)
            ·
              refine ⟨1666882048421209954256003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4445018795789893211349341 1666882048421209954256003)
              ·
                refine ⟨2500323072631814931384005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1666882048421209954256003 2500323072631814931384005)
                ·
                  refine ⟨468810576118465299634501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500323072631814931384005 468810576118465299634501)
                  ·
                    rfl

theorem cell21_2054262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_2054262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054262 prefixEnd_2054262 := by exact prefixLift 2054262
  have htrace : WordTrace (prefixWord ++ tailWord_2054262) baseStart_2054262 baseEnd_2054262 := by
    simpa [prefixWord, tailWord_2054262, baseEnd_2054262] using wordTrace_append hprefix tailTrace_2054262
  have hstable : (prefixWord ++ tailWord_2054262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054262).length < 2 ^ (prefixWord ++ tailWord_2054262).sum := by decide
  have hdescent : baseEnd_2054262 < baseStart_2054262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054321 : List Nat := [1, 2, 2, 5, 2, 1, 1, 3, 4]
def baseStart_2054321 : Nat := 118140960795 + 2054321 * 2 ^ 59
def prefixEnd_2054321 : Nat := 4983230072969 + 3 ^ 40 * 2054321 * 2
def baseEnd_2054321 : Nat := 468824040722294308151047

theorem tailTrace_2054321 : CollatzResearch.WordTrace tailWord_2054321 prefixEnd_2054321 468824040722294308151047 := by
  unfold tailWord_2054321
  simp only [CollatzResearch.WordTrace]
  refine ⟨74927242390553341939306817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49951494927035561292871211 74927242390553341939306817)
  ·
    refine ⟨56195431792915006454480113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74927242390553341939306817 56195431792915006454480113)
    ·
      refine ⟨42146573844686254840860085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56195431792915006454480113 42146573844686254840860085)
      ·
        refine ⟨3951241297939336391330633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42146573844686254840860085 3951241297939336391330633)
        ·
          refine ⟨2963430973454502293497975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3951241297939336391330633 2963430973454502293497975)
          ·
            refine ⟨4445146460181753440246963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963430973454502293497975 4445146460181753440246963)
            ·
              refine ⟨6667719690272630160370445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4445146460181753440246963 6667719690272630160370445)
              ·
                refine ⟨2500394883852236310138917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6667719690272630160370445 2500394883852236310138917)
                ·
                  refine ⟨468824040722294308151047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500394883852236310138917 468824040722294308151047)
                  ·
                    rfl

theorem cell21_2054321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_2054321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054321 prefixEnd_2054321 := by exact prefixLift 2054321
  have htrace : WordTrace (prefixWord ++ tailWord_2054321) baseStart_2054321 baseEnd_2054321 := by
    simpa [prefixWord, tailWord_2054321, baseEnd_2054321] using wordTrace_append hprefix tailTrace_2054321
  have hstable : (prefixWord ++ tailWord_2054321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054321).length < 2 ^ (prefixWord ++ tailWord_2054321).sum := by decide
  have hdescent : baseEnd_2054321 < baseStart_2054321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054363 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 4]
def baseStart_2054363 : Nat := 118140960795 + 2054363 * 2 ^ 59
def prefixEnd_2054363 : Nat := 4983230072969 + 3 ^ 40 * 2054363 * 2
def baseEnd_2054363 : Nat := 468833625694511568450961

theorem tailTrace_2054363 : CollatzResearch.WordTrace tailWord_2054363 prefixEnd_2054363 468833625694511568450961 := by
  unfold tailWord_2054363
  simp only [CollatzResearch.WordTrace]
  refine ⟨74928774256401183112335743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49952516170934122074890495 74928774256401183112335743)
  ·
    refine ⟨112393161384601774668503615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74928774256401183112335743 112393161384601774668503615)
    ·
      refine ⟨168589742076902662002755423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112393161384601774668503615 168589742076902662002755423)
      ·
        refine ⟨252884613115353993004133135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168589742076902662002755423 252884613115353993004133135)
        ·
          refine ⟨379326919673030989506199703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252884613115353993004133135 379326919673030989506199703)
          ·
            refine ⟨568990379509546484259299555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379326919673030989506199703 568990379509546484259299555)
            ·
              refine ⟨853485569264319726388949333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568990379509546484259299555 853485569264319726388949333)
              ·
                refine ⟨2500446003704061698405125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 853485569264319726388949333 2500446003704061698405125)
                ·
                  refine ⟨468833625694511568450961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500446003704061698405125 468833625694511568450961)
                  ·
                    rfl

theorem cell21_2054363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 4].length) (baseStart_2054363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054363 prefixEnd_2054363 := by exact prefixLift 2054363
  have htrace : WordTrace (prefixWord ++ tailWord_2054363) baseStart_2054363 baseEnd_2054363 := by
    simpa [prefixWord, tailWord_2054363, baseEnd_2054363] using wordTrace_append hprefix tailTrace_2054363
  have hstable : (prefixWord ++ tailWord_2054363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054363).length < 2 ^ (prefixWord ++ tailWord_2054363).sum := by decide
  have hdescent : baseEnd_2054363 < baseStart_2054363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054445 : List Nat := [1, 5, 3, 1, 2, 2, 2, 5]
def baseStart_2054445 : Nat := 118140960795 + 2054445 * 2 ^ 59
def prefixEnd_2054445 : Nat := 4983230072969 + 3 ^ 40 * 2054445 * 2
def baseEnd_2054445 : Nat := 156284113070565882694709

theorem tailTrace_2054445 : CollatzResearch.WordTrace tailWord_2054445 prefixEnd_2054445 156284113070565882694709 := by
  unfold tailWord_2054445
  simp only [CollatzResearch.WordTrace]
  refine ⟨74931765042104111116820789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49954510028069407411213859 74931765042104111116820789)
  ·
    refine ⟨7024852972697260417201949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74931765042104111116820789 7024852972697260417201949)
    ·
      refine ⟨2634319864761472656450731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7024852972697260417201949 2634319864761472656450731)
      ·
        refine ⟨3951479797142208984676097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2634319864761472656450731 3951479797142208984676097)
        ·
          refine ⟨2963609847856656738507073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3951479797142208984676097 2963609847856656738507073)
          ·
            refine ⟨2222707385892492553880305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2963609847856656738507073 2222707385892492553880305)
            ·
              refine ⟨1667030539419369415410229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2222707385892492553880305 1667030539419369415410229)
              ·
                refine ⟨156284113070565882694709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1667030539419369415410229 156284113070565882694709)
                ·
                  rfl

theorem cell21_2054445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 5].length) (baseStart_2054445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054445 prefixEnd_2054445 := by exact prefixLift 2054445
  have htrace : WordTrace (prefixWord ++ tailWord_2054445) baseStart_2054445 baseEnd_2054445 := by
    simpa [prefixWord, tailWord_2054445, baseEnd_2054445] using wordTrace_append hprefix tailTrace_2054445
  have hstable : (prefixWord ++ tailWord_2054445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054445).length < 2 ^ (prefixWord ++ tailWord_2054445).sum := by decide
  have hdescent : baseEnd_2054445 < baseStart_2054445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054532 : List Nat := [2, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_2054532 : Nat := 118140960795 + 2054532 * 2 ^ 59
def prefixEnd_2054532 : Nat := 4983230072969 + 3 ^ 40 * 2054532 * 2
def baseEnd_2054532 : Nat := 468872193797004830133949

theorem tailTrace_2054532 : CollatzResearch.WordTrace tailWord_2054532 prefixEnd_2054532 468872193797004830133949 := by
  unfold tailWord_2054532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37467469096394462487618925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49956625461859283316825233 37467469096394462487618925)
  ·
    refine ⟨14050300911147923432857097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37467469096394462487618925 14050300911147923432857097)
    ·
      refine ⟨10537725683360942574642823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14050300911147923432857097 10537725683360942574642823)
      ·
        refine ⟨15806588525041413861964235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10537725683360942574642823 15806588525041413861964235)
        ·
          refine ⟨23709882787562120792946353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15806588525041413861964235 23709882787562120792946353)
          ·
            refine ⟨17782412090671590594709765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23709882787562120792946353 17782412090671590594709765)
            ·
              refine ⟨3334202267000923236508081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17782412090671590594709765 3334202267000923236508081)
              ·
                refine ⟨2500651700250692427381061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3334202267000923236508081 2500651700250692427381061)
                ·
                  refine ⟨468872193797004830133949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2500651700250692427381061 468872193797004830133949)
                  ·
                    rfl

theorem cell21_2054532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_2054532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054532 prefixEnd_2054532 := by exact prefixLift 2054532
  have htrace : WordTrace (prefixWord ++ tailWord_2054532) baseStart_2054532 baseEnd_2054532 := by
    simpa [prefixWord, tailWord_2054532, baseEnd_2054532] using wordTrace_append hprefix tailTrace_2054532
  have hstable : (prefixWord ++ tailWord_2054532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054532).length < 2 ^ (prefixWord ++ tailWord_2054532).sum := by decide
  have hdescent : baseEnd_2054532 < baseStart_2054532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054560 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_2054560 : Nat := 118140960795 + 2054560 * 2 ^ 59
def prefixEnd_2054560 : Nat := 4983230072969 + 3 ^ 40 * 2054560 * 2
def baseEnd_2054560 : Nat := 468878583778483003667225

theorem tailTrace_2054560 : CollatzResearch.WordTrace tailWord_2054560 prefixEnd_2054560 468878583778483003667225 := by
  unfold tailWord_2054560
  simp only [CollatzResearch.WordTrace]
  refine ⟨37467979718343742878628567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49957306291124990504838089 37467979718343742878628567)
  ·
    refine ⟨56201969577515614317942851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37467979718343742878628567 56201969577515614317942851)
    ·
      refine ⟨84302954366273421476914277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56201969577515614317942851 84302954366273421476914277)
      ·
        refine ⟨15806803943676266526921427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84302954366273421476914277 15806803943676266526921427)
        ·
          refine ⟨23710205915514399790382141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15806803943676266526921427 23710205915514399790382141)
          ·
            refine ⟨8891327218317899921393303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23710205915514399790382141 8891327218317899921393303)
            ·
              refine ⟨13336990827476849882089955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8891327218317899921393303 13336990827476849882089955)
              ·
                refine ⟨20005486241215274823134933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13336990827476849882089955 20005486241215274823134933)
                ·
                  refine ⟨468878583778483003667225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20005486241215274823134933 468878583778483003667225)
                  ·
                    rfl

theorem cell21_2054560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_2054560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054560 prefixEnd_2054560 := by exact prefixLift 2054560
  have htrace : WordTrace (prefixWord ++ tailWord_2054560) baseStart_2054560 baseEnd_2054560 := by
    simpa [prefixWord, tailWord_2054560, baseEnd_2054560] using wordTrace_append hprefix tailTrace_2054560
  have hstable : (prefixWord ++ tailWord_2054560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054560).length < 2 ^ (prefixWord ++ tailWord_2054560).sum := by decide
  have hdescent : baseEnd_2054560 < baseStart_2054560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054580 : List Nat := [2, 5, 2, 2, 1, 1, 8]
def baseStart_2054580 : Nat := 118140960795 + 2054580 * 2 ^ 59
def prefixEnd_2054580 : Nat := 4983230072969 + 3 ^ 40 * 2054580 * 2
def baseEnd_2054580 : Nat := 52098127561218601481539

theorem tailTrace_2054580 : CollatzResearch.WordTrace tailWord_2054580 prefixEnd_2054580 52098127561218601481539 := by
  unfold tailWord_2054580
  simp only [CollatzResearch.WordTrace]
  refine ⟨37468344448307514586492597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49957792597743352781990129 37468344448307514586492597)
  ·
    refine ⟨3512657292028829492483681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37468344448307514586492597 3512657292028829492483681)
    ·
      refine ⟨2634492969021622119362761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3512657292028829492483681 2634492969021622119362761)
      ·
        refine ⟨1975869726766216589522071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2634492969021622119362761 1975869726766216589522071)
        ·
          refine ⟨2963804590149324884283107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1975869726766216589522071 2963804590149324884283107)
          ·
            refine ⟨4445706885223987326424661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2963804590149324884283107 4445706885223987326424661)
            ·
              refine ⟨52098127561218601481539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4445706885223987326424661 52098127561218601481539)
              ·
                rfl

theorem cell21_2054580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 8].length) (baseStart_2054580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054580 prefixEnd_2054580 := by exact prefixLift 2054580
  have htrace : WordTrace (prefixWord ++ tailWord_2054580) baseStart_2054580 baseEnd_2054580 := by
    simpa [prefixWord, tailWord_2054580, baseEnd_2054580] using wordTrace_append hprefix tailTrace_2054580
  have hstable : (prefixWord ++ tailWord_2054580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054580).length < 2 ^ (prefixWord ++ tailWord_2054580).sum := by decide
  have hdescent : baseEnd_2054580 < baseStart_2054580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054712 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_2054712 : Nat := 118140960795 + 2054712 * 2 ^ 59
def prefixEnd_2054712 : Nat := 4983230072969 + 3 ^ 40 * 2054712 * 2
def baseEnd_2054712 : Nat := 468913272249364517133581

theorem tailTrace_2054712 : CollatzResearch.WordTrace tailWord_2054712 prefixEnd_2054712 468913272249364517133581 := by
  unfold tailWord_2054712
  simp only [CollatzResearch.WordTrace]
  refine ⟨37470751666068407858395195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49961002221424543811193593 37470751666068407858395195)
  ·
    refine ⟨56206127499102611787592793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37470751666068407858395195 56206127499102611787592793)
    ·
      refine ⟨42154595624326958840694595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56206127499102611787592793 42154595624326958840694595)
      ·
        refine ⟨63231893436490438261041893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42154595624326958840694595 63231893436490438261041893)
        ·
          refine ⟨11855980019341957173945355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63231893436490438261041893 11855980019341957173945355)
          ·
            refine ⟨17783970029012935760918033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11855980019341957173945355 17783970029012935760918033)
            ·
              refine ⟨13337977521759701820688525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17783970029012935760918033 13337977521759701820688525)
              ·
                refine ⟨5001741570659888182758197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13337977521759701820688525 5001741570659888182758197)
                ·
                  refine ⟨468913272249364517133581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5001741570659888182758197 468913272249364517133581)
                  ·
                    rfl

theorem cell21_2054712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_2054712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054712 prefixEnd_2054712 := by exact prefixLift 2054712
  have htrace : WordTrace (prefixWord ++ tailWord_2054712) baseStart_2054712 baseEnd_2054712 := by
    simpa [prefixWord, tailWord_2054712, baseEnd_2054712] using wordTrace_append hprefix tailTrace_2054712
  have hstable : (prefixWord ++ tailWord_2054712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054712).length < 2 ^ (prefixWord ++ tailWord_2054712).sum := by decide
  have hdescent : baseEnd_2054712 < baseStart_2054712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054760 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_2054760 : Nat := 118140960795 + 2054760 * 2 ^ 59
def prefixEnd_2054760 : Nat := 4983230072969 + 3 ^ 40 * 2054760 * 2
def baseEnd_2054760 : Nat := 468924226503327100333483

theorem tailTrace_2054760 : CollatzResearch.WordTrace tailWord_2054760 prefixEnd_2054760 468924226503327100333483 := by
  unfold tailWord_2054760
  simp only [CollatzResearch.WordTrace]
  refine ⟨37471627017981459957268867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49962169357308613276358489 37471627017981459957268867)
  ·
    refine ⟨56207440526972189935903301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37471627017981459957268867 56207440526972189935903301)
    ·
      refine ⟨10538895098807285612981869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56207440526972189935903301 10538895098807285612981869)
      ·
        refine ⟨3952085662052732104868201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10538895098807285612981869 3952085662052732104868201)
        ·
          refine ⟨2964064246539549078651151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3952085662052732104868201 2964064246539549078651151)
          ·
            refine ⟨4446096369809323617976727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964064246539549078651151 4446096369809323617976727)
            ·
              refine ⟨6669144554713985426965091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446096369809323617976727 6669144554713985426965091)
              ·
                refine ⟨10003716832070978140447637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6669144554713985426965091 10003716832070978140447637)
                ·
                  refine ⟨468924226503327100333483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10003716832070978140447637 468924226503327100333483)
                  ·
                    rfl

theorem cell21_2054760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_2054760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054760 prefixEnd_2054760 := by exact prefixLift 2054760
  have htrace : WordTrace (prefixWord ++ tailWord_2054760) baseStart_2054760 baseEnd_2054760 := by
    simpa [prefixWord, tailWord_2054760, baseEnd_2054760] using wordTrace_append hprefix tailTrace_2054760
  have hstable : (prefixWord ++ tailWord_2054760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054760).length < 2 ^ (prefixWord ++ tailWord_2054760).sum := by decide
  have hdescent : baseEnd_2054760 < baseStart_2054760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054895 : List Nat := [1, 1, 2, 1, 5, 2, 2, 3, 4]
def baseStart_2054895 : Nat := 118140960795 + 2054895 * 2 ^ 59
def prefixEnd_2054895 : Nat := 4983230072969 + 3 ^ 40 * 2054895 * 2
def baseEnd_2054895 : Nat := 468955035342596865583207

theorem tailTrace_2054895 : CollatzResearch.WordTrace tailWord_2054895 prefixEnd_2054895 468955035342596865583207 := by
  unfold tailWord_2054895
  simp only [CollatzResearch.WordTrace]
  refine ⟨74948177890473837970702139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49965451926982558647134759 74948177890473837970702139)
  ·
    refine ⟨112422266835710756956053209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74948177890473837970702139 112422266835710756956053209)
    ·
      refine ⟨84316700126783067717039907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112422266835710756956053209 84316700126783067717039907)
      ·
        refine ⟨126475050190174601575559861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84316700126783067717039907 126475050190174601575559861)
        ·
          refine ⟨11857035955328868897708737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126475050190174601575559861 11857035955328868897708737)
          ·
            refine ⟨8892776966496651673281553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11857035955328868897708737 8892776966496651673281553)
            ·
              refine ⟨6669582724872488754961165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8892776966496651673281553 6669582724872488754961165)
              ·
                refine ⟨2501093521827183283110437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6669582724872488754961165 2501093521827183283110437)
                ·
                  refine ⟨468955035342596865583207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2501093521827183283110437 468955035342596865583207)
                  ·
                    rfl

theorem cell21_2054895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 4].length) (baseStart_2054895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054895 prefixEnd_2054895 := by exact prefixLift 2054895
  have htrace : WordTrace (prefixWord ++ tailWord_2054895) baseStart_2054895 baseEnd_2054895 := by
    simpa [prefixWord, tailWord_2054895, baseEnd_2054895] using wordTrace_append hprefix tailTrace_2054895
  have hstable : (prefixWord ++ tailWord_2054895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054895).length < 2 ^ (prefixWord ++ tailWord_2054895).sum := by decide
  have hdescent : baseEnd_2054895 < baseStart_2054895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054901 : List Nat := [1, 3, 6, 1, 1, 1, 3, 5]
def baseStart_2054901 : Nat := 118140960795 + 2054901 * 2 ^ 59
def prefixEnd_2054901 : Nat := 4983230072969 + 3 ^ 40 * 2054901 * 2
def baseEnd_2054901 : Nat := 156318801541447396161065

theorem tailTrace_2054901 : CollatzResearch.WordTrace tailWord_2054901 prefixEnd_2054901 156318801541447396161065 := by
  unfold tailWord_2054901
  simp only [CollatzResearch.WordTrace]
  refine ⟨74948396728452100995420557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49965597818968067330280371 74948396728452100995420557)
  ·
    refine ⟨28105648773169537873282709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74948396728452100995420557 28105648773169537873282709)
    ·
      refine ⟨1317452286242322087810127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28105648773169537873282709 1317452286242322087810127)
      ·
        refine ⟨1976178429363483131715191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317452286242322087810127 1976178429363483131715191)
        ·
          refine ⟨2964267644045224697572787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976178429363483131715191 2964267644045224697572787)
          ·
            refine ⟨4446401466067837046359181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2964267644045224697572787 4446401466067837046359181)
            ·
              refine ⟨1667400549775438892384693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4446401466067837046359181 1667400549775438892384693)
              ·
                refine ⟨156318801541447396161065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1667400549775438892384693 156318801541447396161065)
                ·
                  rfl

theorem cell21_2054901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 5].length) (baseStart_2054901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054901 prefixEnd_2054901 := by exact prefixLift 2054901
  have htrace : WordTrace (prefixWord ++ tailWord_2054901) baseStart_2054901 baseEnd_2054901 := by
    simpa [prefixWord, tailWord_2054901, baseEnd_2054901] using wordTrace_append hprefix tailTrace_2054901
  have hstable : (prefixWord ++ tailWord_2054901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054901).length < 2 ^ (prefixWord ++ tailWord_2054901).sum := by decide
  have hdescent : baseEnd_2054901 < baseStart_2054901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054923 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 9]
def baseStart_2054923 : Nat := 118140960795 + 2054923 * 2 ^ 59
def prefixEnd_2054923 : Nat := 4983230072969 + 3 ^ 40 * 2054923 * 2
def baseEnd_2054923 : Nat := 468961425324075039116483

theorem tailTrace_2054923 : CollatzResearch.WordTrace tailWord_2054923 prefixEnd_2054923 468961425324075039116483 := by
  unfold tailWord_2054923
  simp only [CollatzResearch.WordTrace]
  refine ⟨74949199134372398752721423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49966132756248265835147615 74949199134372398752721423)
  ·
    refine ⟨112423798701558598129082135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74949199134372398752721423 112423798701558598129082135)
    ·
      refine ⟨168635698052337897193623203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112423798701558598129082135 168635698052337897193623203)
      ·
        refine ⟨252953547078506845790434805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168635698052337897193623203 252953547078506845790434805)
        ·
          refine ⟨23714395038610016792853263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252953547078506845790434805 23714395038610016792853263)
          ·
            refine ⟨35571592557915025189279895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23714395038610016792853263 35571592557915025189279895)
            ·
              refine ⟨53357388836872537783919843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35571592557915025189279895 53357388836872537783919843)
              ·
                refine ⟨80036083255308806675879765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53357388836872537783919843 80036083255308806675879765)
                ·
                  refine ⟨468961425324075039116483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80036083255308806675879765 468961425324075039116483)
                  ·
                    rfl

theorem cell21_2054923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_2054923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054923 prefixEnd_2054923 := by exact prefixLift 2054923
  have htrace : WordTrace (prefixWord ++ tailWord_2054923) baseStart_2054923 baseEnd_2054923 := by
    simpa [prefixWord, tailWord_2054923, baseEnd_2054923] using wordTrace_append hprefix tailTrace_2054923
  have hstable : (prefixWord ++ tailWord_2054923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054923).length < 2 ^ (prefixWord ++ tailWord_2054923).sum := by decide
  have hdescent : baseEnd_2054923 < baseStart_2054923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054940 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_2054940 : Nat := 118140960795 + 2054940 * 2 ^ 59
def prefixEnd_2054940 : Nat := 4983230072969 + 3 ^ 40 * 2054940 * 2
def baseEnd_2054940 : Nat := 468965304955686787333115

theorem tailTrace_2054940 : CollatzResearch.WordTrace tailWord_2054940 prefixEnd_2054940 468965304955686787333115 := by
  unfold tailWord_2054940
  simp only [CollatzResearch.WordTrace]
  refine ⟨37474909587655405328045137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49966546116873873770726849 37474909587655405328045137)
  ·
    refine ⟨28106182190741553996033853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37474909587655405328045137 28106182190741553996033853)
    ·
      refine ⟨10539818321528082748512695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28106182190741553996033853 10539818321528082748512695)
      ·
        refine ⟨15809727482292124122769043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10539818321528082748512695 15809727482292124122769043)
        ·
          refine ⟨23714591223438186184153565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15809727482292124122769043 23714591223438186184153565)
          ·
            refine ⟨8892971708789319819057587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23714591223438186184153565 8892971708789319819057587)
            ·
              refine ⟨13339457563183979728586381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8892971708789319819057587 13339457563183979728586381)
              ·
                refine ⟨5002296586193992398219893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13339457563183979728586381 5002296586193992398219893)
                ·
                  refine ⟨468965304955686787333115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5002296586193992398219893 468965304955686787333115)
                  ·
                    rfl

theorem cell21_2054940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_2054940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054940 prefixEnd_2054940 := by exact prefixLift 2054940
  have htrace : WordTrace (prefixWord ++ tailWord_2054940) baseStart_2054940 baseEnd_2054940 := by
    simpa [prefixWord, tailWord_2054940, baseEnd_2054940] using wordTrace_append hprefix tailTrace_2054940
  have hstable : (prefixWord ++ tailWord_2054940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054940).length < 2 ^ (prefixWord ++ tailWord_2054940).sum := by decide
  have hdescent : baseEnd_2054940 < baseStart_2054940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2054985 : List Nat := [1, 2, 1, 1, 2, 7, 7]
def baseStart_2054985 : Nat := 118140960795 + 2054985 * 2 ^ 59
def prefixEnd_2054985 : Nat := 4983230072969 + 3 ^ 40 * 2054985 * 2
def baseEnd_2054985 : Nat := 52108397174308523231447

theorem tailTrace_2054985 : CollatzResearch.WordTrace tailWord_2054985 prefixEnd_2054985 52108397174308523231447 := by
  unfold tailWord_2054985
  simp only [CollatzResearch.WordTrace]
  refine ⟨74951460460147783341478409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49967640306765188894318939 74951460460147783341478409)
  ·
    refine ⟨56213595345110837506108807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74951460460147783341478409 56213595345110837506108807)
    ·
      refine ⟨84320393017666256259163211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56213595345110837506108807 84320393017666256259163211)
      ·
        refine ⟨126480589526499384388744817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84320393017666256259163211 126480589526499384388744817)
        ·
          refine ⟨94860442144874538291558613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126480589526499384388744817 94860442144874538291558613)
          ·
            refine ⟨2223291612770496991208405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 94860442144874538291558613 2223291612770496991208405)
            ·
              refine ⟨52108397174308523231447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2223291612770496991208405 52108397174308523231447)
              ·
                rfl

theorem cell21_2054985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 7].length) (baseStart_2054985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2054985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2054985 prefixEnd_2054985 := by exact prefixLift 2054985
  have htrace : WordTrace (prefixWord ++ tailWord_2054985) baseStart_2054985 baseEnd_2054985 := by
    simpa [prefixWord, tailWord_2054985, baseEnd_2054985] using wordTrace_append hprefix tailTrace_2054985
  have hstable : (prefixWord ++ tailWord_2054985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2054985).length < 2 ^ (prefixWord ++ tailWord_2054985).sum := by decide
  have hdescent : baseEnd_2054985 < baseStart_2054985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2054985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055042 : List Nat := [3, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2055042 : Nat := 118140960795 + 2055042 * 2 ^ 59
def prefixEnd_2055042 : Nat := 4983230072969 + 3 ^ 40 * 2055042 * 2
def baseEnd_2055042 : Nat := 468988582745357276632907

theorem tailTrace_2055042 : CollatzResearch.WordTrace tailWord_2055042 prefixEnd_2055042 468988582745357276632907 := by
  unfold tailWord_2055042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18738384855235320519075845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49969026280627521384202253 18738384855235320519075845)
  ·
    refine ⟨3513447160356622597326721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18738384855235320519075845 3513447160356622597326721)
    ·
      refine ⟨2635085370267466947995041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3513447160356622597326721 2635085370267466947995041)
      ·
        refine ⟨1976314027700600210996281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2635085370267466947995041 1976314027700600210996281)
        ·
          refine ⟨1482235520775450158247211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1976314027700600210996281 1482235520775450158247211)
          ·
            refine ⟨2223353281163175237370817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482235520775450158247211 2223353281163175237370817)
            ·
              refine ⟨1667514960872381428028113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223353281163175237370817 1667514960872381428028113)
              ·
                refine ⟨1250636220654286071021085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1667514960872381428028113 1250636220654286071021085)
                ·
                  refine ⟨468988582745357276632907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250636220654286071021085 468988582745357276632907)
                  ·
                    rfl

theorem cell21_2055042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2055042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055042 prefixEnd_2055042 := by exact prefixLift 2055042
  have htrace : WordTrace (prefixWord ++ tailWord_2055042) baseStart_2055042 baseEnd_2055042 := by
    simpa [prefixWord, tailWord_2055042, baseEnd_2055042] using wordTrace_append hprefix tailTrace_2055042
  have hstable : (prefixWord ++ tailWord_2055042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055042).length < 2 ^ (prefixWord ++ tailWord_2055042).sum := by decide
  have hdescent : baseEnd_2055042 < baseStart_2055042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055047 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 4]
def baseStart_2055047 : Nat := 118140960795 + 2055047 * 2 ^ 59
def prefixEnd_2055047 : Nat := 4983230072969 + 3 ^ 40 * 2055047 * 2
def baseEnd_2055047 : Nat := 468989723813478379049563

theorem tailTrace_2055047 : CollatzResearch.WordTrace tailWord_2055047 prefixEnd_2055047 468989723813478379049563 := by
  unfold tailWord_2055047
  simp only [CollatzResearch.WordTrace]
  refine ⟨74953721785923167930235395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49969147857282111953490263 74953721785923167930235395)
  ·
    refine ⟨112430582678884751895353093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74953721785923167930235395 112430582678884751895353093)
    ·
      refine ⟨21080734252290890980378705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112430582678884751895353093 21080734252290890980378705)
      ·
        refine ⟨15810550689218168235284029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21080734252290890980378705 15810550689218168235284029)
        ·
          refine ⟨5928956508456813088231511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15810550689218168235284029 5928956508456813088231511)
          ·
            refine ⟨8893434762685219632347267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5928956508456813088231511 8893434762685219632347267)
            ·
              refine ⟨13340152144027829448520901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8893434762685219632347267 13340152144027829448520901)
              ·
                refine ⟨2501278527005218021597669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13340152144027829448520901 2501278527005218021597669)
                ·
                  refine ⟨468989723813478379049563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2501278527005218021597669 468989723813478379049563)
                  ·
                    rfl

theorem cell21_2055047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 4].length) (baseStart_2055047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055047 prefixEnd_2055047 := by exact prefixLift 2055047
  have htrace : WordTrace (prefixWord ++ tailWord_2055047) baseStart_2055047 baseEnd_2055047 := by
    simpa [prefixWord, tailWord_2055047, baseEnd_2055047] using wordTrace_append hprefix tailTrace_2055047
  have hstable : (prefixWord ++ tailWord_2055047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055047).length < 2 ^ (prefixWord ++ tailWord_2055047).sum := by decide
  have hdescent : baseEnd_2055047 < baseStart_2055047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055050 : List Nat := [3, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_2055050 : Nat := 118140960795 + 2055050 * 2 ^ 59
def prefixEnd_2055050 : Nat := 4983230072969 + 3 ^ 40 * 2055050 * 2
def baseEnd_2055050 : Nat := 468990408454351040499557

theorem tailTrace_2055050 : CollatzResearch.WordTrace tailWord_2055050 prefixEnd_2055050 468990408454351040499557 := by
  unfold tailWord_2055050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18738457801228074860648651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49969220803274866295063069 18738457801228074860648651)
  ·
    refine ⟨28107686701842112290972977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18738457801228074860648651 28107686701842112290972977)
    ·
      refine ⟨21080765026381584218229733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28107686701842112290972977 21080765026381584218229733)
      ·
        refine ⟨3952643442446547040918075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21080765026381584218229733 3952643442446547040918075)
        ·
          refine ⟨5928965163669820561377113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3952643442446547040918075 5928965163669820561377113)
          ·
            refine ⟨4446723872752365421032835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5928965163669820561377113 4446723872752365421032835)
            ·
              refine ⟨6670085809128548131549253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4446723872752365421032835 6670085809128548131549253)
              ·
                refine ⟨1250641089211602774665485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6670085809128548131549253 1250641089211602774665485)
                ·
                  refine ⟨468990408454351040499557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250641089211602774665485 468990408454351040499557)
                  ·
                    rfl

theorem cell21_2055050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_2055050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055050 prefixEnd_2055050 := by exact prefixLift 2055050
  have htrace : WordTrace (prefixWord ++ tailWord_2055050) baseStart_2055050 baseEnd_2055050 := by
    simpa [prefixWord, tailWord_2055050, baseEnd_2055050] using wordTrace_append hprefix tailTrace_2055050
  have hstable : (prefixWord ++ tailWord_2055050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055050).length < 2 ^ (prefixWord ++ tailWord_2055050).sum := by decide
  have hdescent : baseEnd_2055050 < baseStart_2055050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055061 : List Nat := [1, 3, 2, 1, 1, 4, 3, 6]
def baseStart_2055061 : Nat := 118140960795 + 2055061 * 2 ^ 59
def prefixEnd_2055061 : Nat := 4983230072969 + 3 ^ 40 * 2055061 * 2
def baseEnd_2055061 : Nat := 156330972934739155272067

theorem tailTrace_2055061 : CollatzResearch.WordTrace tailWord_2055061 prefixEnd_2055061 156330972934739155272067 := by
  unfold tailWord_2055061
  simp only [CollatzResearch.WordTrace]
  refine ⟨74954232407872448321245037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49969488271914965547496691 74954232407872448321245037)
  ·
    refine ⟨28107837152952168120466889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74954232407872448321245037 28107837152952168120466889)
    ·
      refine ⟨21080877864714126090350167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28107837152952168120466889 21080877864714126090350167)
      ·
        refine ⟨31621316797071189135525251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21080877864714126090350167 31621316797071189135525251)
        ·
          refine ⟨47431975195606783703287877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31621316797071189135525251 47431975195606783703287877)
          ·
            refine ⟨8893495349176271944366477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47431975195606783703287877 8893495349176271944366477)
            ·
              refine ⟨3335060755941101979137429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8893495349176271944366477 3335060755941101979137429)
              ·
                refine ⟨156330972934739155272067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3335060755941101979137429 156330972934739155272067)
                ·
                  rfl

theorem cell21_2055061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 6].length) (baseStart_2055061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055061 prefixEnd_2055061 := by exact prefixLift 2055061
  have htrace : WordTrace (prefixWord ++ tailWord_2055061) baseStart_2055061 baseEnd_2055061 := by
    simpa [prefixWord, tailWord_2055061, baseEnd_2055061] using wordTrace_append hprefix tailTrace_2055061
  have hstable : (prefixWord ++ tailWord_2055061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055061).length < 2 ^ (prefixWord ++ tailWord_2055061).sum := by decide
  have hdescent : baseEnd_2055061 < baseStart_2055061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055075 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 7]
def baseStart_2055075 : Nat := 118140960795 + 2055075 * 2 ^ 59
def prefixEnd_2055075 : Nat := 4983230072969 + 3 ^ 40 * 2055075 * 2
def baseEnd_2055075 : Nat := 468996113794956552582839

theorem tailTrace_2055075 : CollatzResearch.WordTrace tailWord_2055075 prefixEnd_2055075 468996113794956552582839 := by
  unfold tailWord_2055075
  simp only [CollatzResearch.WordTrace]
  refine ⟨74954743029821728712254679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49969828686547819141503119 74954743029821728712254679)
  ·
    refine ⟨112432114544732593068382019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74954743029821728712254679 112432114544732593068382019)
    ·
      refine ⟨168648171817098889602573029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112432114544732593068382019 168648171817098889602573029)
      ·
        refine ⟨31621532215706041800482443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168648171817098889602573029 31621532215706041800482443)
        ·
          refine ⟨47432298323559062700723665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31621532215706041800482443 47432298323559062700723665)
          ·
            refine ⟨35574223742669297025542749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47432298323559062700723665 35574223742669297025542749)
            ·
              refine ⟨13340333903500986384578531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35574223742669297025542749 13340333903500986384578531)
              ·
                refine ⟨20010500855251479576867797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13340333903500986384578531 20010500855251479576867797)
                ·
                  refine ⟨468996113794956552582839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20010500855251479576867797 468996113794956552582839)
                  ·
                    rfl

theorem cell21_2055075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_2055075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055075 prefixEnd_2055075 := by exact prefixLift 2055075
  have htrace : WordTrace (prefixWord ++ tailWord_2055075) baseStart_2055075 baseEnd_2055075 := by
    simpa [prefixWord, tailWord_2055075, baseEnd_2055075] using wordTrace_append hprefix tailTrace_2055075
  have hstable : (prefixWord ++ tailWord_2055075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055075).length < 2 ^ (prefixWord ++ tailWord_2055075).sum := by decide
  have hdescent : baseEnd_2055075 < baseStart_2055075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055120 : List Nat := [2, 1, 1, 1, 1, 2, 3, 10]
def baseStart_2055120 : Nat := 118140960795 + 2055120 * 2 ^ 59
def prefixEnd_2055120 : Nat := 4983230072969 + 3 ^ 40 * 2055120 * 2
def baseEnd_2055120 : Nat := 156335461136015491444249

theorem tailTrace_2055120 : CollatzResearch.WordTrace tailWord_2055120 prefixEnd_2055120 156335461136015491444249 := by
  unfold tailWord_2055120
  simp only [CollatzResearch.WordTrace]
  refine ⟨37478192157329350698821407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49970922876439134265095209 37478192157329350698821407)
  ·
    refine ⟨56217288235994026048232111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37478192157329350698821407 56217288235994026048232111)
    ·
      refine ⟨84325932353991039072348167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56217288235994026048232111 84325932353991039072348167)
      ·
        refine ⟨126488898530986558608522251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84325932353991039072348167 126488898530986558608522251)
        ·
          refine ⟨189733347796479837912783377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126488898530986558608522251 189733347796479837912783377)
          ·
            refine ⟨142300010847359878434587533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189733347796479837912783377 142300010847359878434587533)
            ·
              refine ⟨53362504067759954412970325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142300010847359878434587533 53362504067759954412970325)
              ·
                refine ⟨156335461136015491444249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53362504067759954412970325 156335461136015491444249)
                ·
                  rfl

theorem cell21_2055120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_2055120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055120 prefixEnd_2055120 := by exact prefixLift 2055120
  have htrace : WordTrace (prefixWord ++ tailWord_2055120) baseStart_2055120 baseEnd_2055120 := by
    simpa [prefixWord, tailWord_2055120, baseEnd_2055120] using wordTrace_append hprefix tailTrace_2055120
  have hstable : (prefixWord ++ tailWord_2055120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055120).length < 2 ^ (prefixWord ++ tailWord_2055120).sum := by decide
  have hdescent : baseEnd_2055120 < baseStart_2055120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055230 : List Nat := [4, 2, 1, 3, 1, 1, 3, 6]
def baseStart_2055230 : Nat := 118140960795 + 2055230 * 2 ^ 59
def prefixEnd_2055230 : Nat := 4983230072969 + 3 ^ 40 * 2055230 * 2
def baseEnd_2055230 : Nat := 156343828968903575833063

theorem tailTrace_2055230 : CollatzResearch.WordTrace tailWord_2055230 prefixEnd_2055230 156343828968903575833063 := by
  unfold tailWord_2055230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9370049543032523773018393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49973597562840126789431429 9370049543032523773018393)
  ·
    refine ⟨7027537157274392829763795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9370049543032523773018393 7027537157274392829763795)
    ·
      refine ⟨10541305735911589244645693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7027537157274392829763795 10541305735911589244645693)
      ·
        refine ⟨3952989650966845966742135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10541305735911589244645693 3952989650966845966742135)
        ·
          refine ⟨5929484476450268950113203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3952989650966845966742135 5929484476450268950113203)
          ·
            refine ⟨8894226714675403425169805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5929484476450268950113203 8894226714675403425169805)
            ·
              refine ⟨3335335018003276284438677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8894226714675403425169805 3335335018003276284438677)
              ·
                refine ⟨156343828968903575833063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3335335018003276284438677 156343828968903575833063)
                ·
                  rfl

theorem cell21_2055230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_2055230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055230 prefixEnd_2055230 := by exact prefixLift 2055230
  have htrace : WordTrace (prefixWord ++ tailWord_2055230) baseStart_2055230 baseEnd_2055230 := by
    simpa [prefixWord, tailWord_2055230, baseEnd_2055230] using wordTrace_append hprefix tailTrace_2055230
  have hstable : (prefixWord ++ tailWord_2055230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055230).length < 2 ^ (prefixWord ++ tailWord_2055230).sum := by decide
  have hdescent : baseEnd_2055230 < baseStart_2055230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055382 : List Nat := [5, 2, 1, 2, 2, 9]
def baseStart_2055382 : Nat := 118140960795 + 2055382 * 2 ^ 59
def prefixEnd_2055382 : Nat := 4983230072969 + 3 ^ 40 * 2055382 * 2
def baseEnd_2055382 : Nat := 17372821310281194109835

theorem tailTrace_2055382 : CollatzResearch.WordTrace tailWord_2055382 prefixEnd_2055382 17372821310281194109835 := by
  unfold tailWord_2055382
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685371264981845008980025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49977293493139680095786933 4685371264981845008980025)
  ·
    refine ⟨3514028448736383756735019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4685371264981845008980025 3514028448736383756735019)
    ·
      refine ⟨5271042673104575635102529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3514028448736383756735019 5271042673104575635102529)
      ·
        refine ⟨3953282004828431726326897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5271042673104575635102529 3953282004828431726326897)
        ·
          refine ⟨2964961503621323794745173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3953282004828431726326897 2964961503621323794745173)
          ·
            refine ⟨17372821310281194109835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2964961503621323794745173 17372821310281194109835)
            ·
              rfl

theorem cell21_2055382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 9].length) (baseStart_2055382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055382 prefixEnd_2055382 := by exact prefixLift 2055382
  have htrace : WordTrace (prefixWord ++ tailWord_2055382) baseStart_2055382 baseEnd_2055382 := by
    simpa [prefixWord, tailWord_2055382, baseEnd_2055382] using wordTrace_append hprefix tailTrace_2055382
  have hstable : (prefixWord ++ tailWord_2055382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055382).length < 2 ^ (prefixWord ++ tailWord_2055382).sum := by decide
  have hdescent : baseEnd_2055382 < baseStart_2055382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055399 : List Nat := [1, 1, 5, 3, 3, 1, 1, 6]
def baseStart_2055399 : Nat := 118140960795 + 2055399 * 2 ^ 59
def prefixEnd_2055399 : Nat := 4983230072969 + 3 ^ 40 * 2055399 * 2
def baseEnd_2055399 : Nat := 156356685003067996394059

theorem tailTrace_2055399 : CollatzResearch.WordTrace tailWord_2055399 prefixEnd_2055399 156356685003067996394059 := by
  unfold tailWord_2055399
  simp only [CollatzResearch.WordTrace]
  refine ⟨74966560280647932047049251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49977706853765288031366167 74966560280647932047049251)
  ·
    refine ⟨112449840420971898070573877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74966560280647932047049251 112449840420971898070573877)
    ·
      refine ⟨10542172539466115444116301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112449840420971898070573877 10542172539466115444116301)
      ·
        refine ⟨3953314702299793291543613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10542172539466115444116301 3953314702299793291543613)
        ·
          refine ⟨1482493013362422484328855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3953314702299793291543613 1482493013362422484328855)
          ·
            refine ⟨2223739520043633726493283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1482493013362422484328855 2223739520043633726493283)
            ·
              refine ⟨3335609280065450589739925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2223739520043633726493283 3335609280065450589739925)
              ·
                refine ⟨156356685003067996394059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3335609280065450589739925 156356685003067996394059)
                ·
                  rfl

theorem cell21_2055399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 6].length) (baseStart_2055399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055399 prefixEnd_2055399 := by exact prefixLift 2055399
  have htrace : WordTrace (prefixWord ++ tailWord_2055399) baseStart_2055399 baseEnd_2055399 := by
    simpa [prefixWord, tailWord_2055399, baseEnd_2055399] using wordTrace_append hprefix tailTrace_2055399
  have hstable : (prefixWord ++ tailWord_2055399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055399).length < 2 ^ (prefixWord ++ tailWord_2055399).sum := by decide
  have hdescent : baseEnd_2055399 < baseStart_2055399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055486 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2055486 : Nat := 118140960795 + 2055486 * 2 ^ 59
def prefixEnd_2055486 : Nat := 4983230072969 + 3 ^ 40 * 2055486 * 2
def baseEnd_2055486 : Nat := 469089909594511171231999

theorem tailTrace_2055486 : CollatzResearch.WordTrace tailWord_2055486 prefixEnd_2055486 469089909594511171231999 := by
  unfold tailWord_2055486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9371216678916593238183289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49979822287555163936977541 9371216678916593238183289)
  ·
    refine ⟨7028412509187444928637467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9371216678916593238183289 7028412509187444928637467)
    ·
      refine ⟨10542618763781167392956201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7028412509187444928637467 10542618763781167392956201)
      ·
        refine ⟨7906964072835875544717151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10542618763781167392956201 7906964072835875544717151)
        ·
          refine ⟨11860446109253813317075727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7906964072835875544717151 11860446109253813317075727)
          ·
            refine ⟨17790669163880719975613591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11860446109253813317075727 17790669163880719975613591)
            ·
              refine ⟨26686003745821079963420387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17790669163880719975613591 26686003745821079963420387)
              ·
                refine ⟨40029005618731619945130581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26686003745821079963420387 40029005618731619945130581)
                ·
                  refine ⟨469089909594511171231999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40029005618731619945130581 469089909594511171231999)
                  ·
                    rfl

theorem cell21_2055486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2055486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055486 prefixEnd_2055486 := by exact prefixLift 2055486
  have htrace : WordTrace (prefixWord ++ tailWord_2055486) baseStart_2055486 baseEnd_2055486 := by
    simpa [prefixWord, tailWord_2055486, baseEnd_2055486] using wordTrace_append hprefix tailTrace_2055486
  have hstable : (prefixWord ++ tailWord_2055486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055486).length < 2 ^ (prefixWord ++ tailWord_2055486).sum := by decide
  have hdescent : baseEnd_2055486 < baseStart_2055486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055500 : List Nat := [2, 2, 1, 3, 2, 2, 9]
def baseStart_2055500 : Nat := 118140960795 + 2055500 * 2 ^ 59
def prefixEnd_2055500 : Nat := 4983230072969 + 3 ^ 40 * 2055500 * 2
def baseEnd_2055500 : Nat := 52121456065027806444293

theorem tailTrace_2055500 : CollatzResearch.WordTrace tailWord_2055500 prefixEnd_2055500 52121456065027806444293 := by
  unfold tailWord_2055500
  simp only [CollatzResearch.WordTrace]
  refine ⟨37485122026641013148237977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49980162702188017530983969 37485122026641013148237977)
  ·
    refine ⟨28113841519980759861178483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37485122026641013148237977 28113841519980759861178483)
    ·
      refine ⟨42170762279971139791767725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28113841519980759861178483 42170762279971139791767725)
      ·
        refine ⟨15814035854989177421912897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42170762279971139791767725 15814035854989177421912897)
        ·
          refine ⟨11860526891241883066434673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15814035854989177421912897 11860526891241883066434673)
          ·
            refine ⟨8895395168431412299826005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11860526891241883066434673 8895395168431412299826005)
            ·
              refine ⟨52121456065027806444293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8895395168431412299826005 52121456065027806444293)
              ·
                rfl

theorem cell21_2055500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 9].length) (baseStart_2055500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055500 prefixEnd_2055500 := by exact prefixLift 2055500
  have htrace : WordTrace (prefixWord ++ tailWord_2055500) baseStart_2055500 baseEnd_2055500 := by
    simpa [prefixWord, tailWord_2055500, baseEnd_2055500] using wordTrace_append hprefix tailTrace_2055500
  have hstable : (prefixWord ++ tailWord_2055500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055500).length < 2 ^ (prefixWord ++ tailWord_2055500).sum := by decide
  have hdescent : baseEnd_2055500 < baseStart_2055500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055520 : List Nat := [2, 1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_2055520 : Nat := 118140960795 + 2055520 * 2 ^ 59
def prefixEnd_2055520 : Nat := 4983230072969 + 3 ^ 40 * 2055520 * 2
def baseEnd_2055520 : Nat := 469097668857734667665263

theorem tailTrace_2055520 : CollatzResearch.WordTrace tailWord_2055520 prefixEnd_2055520 469097668857734667665263 := by
  unfold tailWord_2055520
  simp only [CollatzResearch.WordTrace]
  refine ⟨37485486756604784856102007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49980649008806379808136009 37485486756604784856102007)
  ·
    refine ⟨56228230134907177284153011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37485486756604784856102007 56228230134907177284153011)
    ·
      refine ⟨84342345202360765926229517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56228230134907177284153011 84342345202360765926229517)
      ·
        refine ⟨31628379450885287222336069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84342345202360765926229517 31628379450885287222336069)
        ·
          refine ⟨5930321147040991354188013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31628379450885287222336069 5930321147040991354188013)
          ·
            refine ⟨2223870430140371757820505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5930321147040991354188013 2223870430140371757820505)
            ·
              refine ⟨1667902822605278818365379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2223870430140371757820505 1667902822605278818365379)
              ·
                refine ⟨2501854233907918227548069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667902822605278818365379 2501854233907918227548069)
                ·
                  refine ⟨469097668857734667665263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2501854233907918227548069 469097668857734667665263)
                  ·
                    rfl

theorem cell21_2055520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_2055520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055520 prefixEnd_2055520 := by exact prefixLift 2055520
  have htrace : WordTrace (prefixWord ++ tailWord_2055520) baseStart_2055520 baseEnd_2055520 := by
    simpa [prefixWord, tailWord_2055520, baseEnd_2055520] using wordTrace_append hprefix tailTrace_2055520
  have hstable : (prefixWord ++ tailWord_2055520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055520).length < 2 ^ (prefixWord ++ tailWord_2055520).sum := by decide
  have hdescent : baseEnd_2055520 < baseStart_2055520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055545 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 8]
def baseStart_2055545 : Nat := 118140960795 + 2055545 * 2 ^ 59
def prefixEnd_2055545 : Nat := 4983230072969 + 3 ^ 40 * 2055545 * 2
def baseEnd_2055545 : Nat := 469103374198340179748545

theorem tailTrace_2055545 : CollatzResearch.WordTrace tailWord_2055545 prefixEnd_2055545 469103374198340179748545 := by
  unfold tailWord_2055545
  simp only [CollatzResearch.WordTrace]
  refine ⟨74971885338118998981864089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49981256892079332654576059 74971885338118998981864089)
  ·
    refine ⟨56228914003589249236398067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74971885338118998981864089 56228914003589249236398067)
    ·
      refine ⟨84343371005383873854597101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56228914003589249236398067 84343371005383873854597101)
      ·
        refine ⟨31628764127018952695473913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84343371005383873854597101 31628764127018952695473913)
        ·
          refine ⟨23721573095264214521605435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31628764127018952695473913 23721573095264214521605435)
          ·
            refine ⟨35582359642896321782408153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23721573095264214521605435 35582359642896321782408153)
            ·
              refine ⟨26686769732172241336806115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35582359642896321782408153 26686769732172241336806115)
              ·
                refine ⟨40030154598258362005209173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26686769732172241336806115 40030154598258362005209173)
                ·
                  refine ⟨469103374198340179748545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40030154598258362005209173 469103374198340179748545)
                  ·
                    rfl

theorem cell21_2055545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_2055545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055545 prefixEnd_2055545 := by exact prefixLift 2055545
  have htrace : WordTrace (prefixWord ++ tailWord_2055545) baseStart_2055545 baseEnd_2055545 := by
    simpa [prefixWord, tailWord_2055545, baseEnd_2055545] using wordTrace_append hprefix tailTrace_2055545
  have hstable : (prefixWord ++ tailWord_2055545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055545).length < 2 ^ (prefixWord ++ tailWord_2055545).sum := by decide
  have hdescent : baseEnd_2055545 < baseStart_2055545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055548 : List Nat := [2, 2, 2, 1, 1, 1, 4, 5, 3]
def baseStart_2055548 : Nat := 118140960795 + 2055548 * 2 ^ 59
def prefixEnd_2055548 : Nat := 4983230072969 + 3 ^ 40 * 2055548 * 2
def baseEnd_2055548 : Nat := 469104058839212841198539

theorem tailTrace_2055548 : CollatzResearch.WordTrace tailWord_2055548 prefixEnd_2055548 469104058839212841198539 := by
  unfold tailWord_2055548
  simp only [CollatzResearch.WordTrace]
  refine ⟨37485997378554065247111649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49981329838072086996148865 37485997378554065247111649)
  ·
    refine ⟨28114498033915548935333737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37485997378554065247111649 28114498033915548935333737)
    ·
      refine ⟨21085873525436661701500303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28114498033915548935333737 21085873525436661701500303)
      ·
        refine ⟨31628810288154992552250455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21085873525436661701500303 31628810288154992552250455)
        ·
          refine ⟨47443215432232488828375683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31628810288154992552250455 47443215432232488828375683)
          ·
            refine ⟨71164823148348733242563525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47443215432232488828375683 71164823148348733242563525)
            ·
              refine ⟨13343404340315387482980661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71164823148348733242563525 13343404340315387482980661)
              ·
                refine ⟨1250944156904567576529437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13343404340315387482980661 1250944156904567576529437)
                ·
                  refine ⟨469104058839212841198539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250944156904567576529437 469104058839212841198539)
                  ·
                    rfl

theorem cell21_2055548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_2055548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055548 prefixEnd_2055548 := by exact prefixLift 2055548
  have htrace : WordTrace (prefixWord ++ tailWord_2055548) baseStart_2055548 baseEnd_2055548 := by
    simpa [prefixWord, tailWord_2055548, baseEnd_2055548] using wordTrace_append hprefix tailTrace_2055548
  have hstable : (prefixWord ++ tailWord_2055548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055548).length < 2 ^ (prefixWord ++ tailWord_2055548).sum := by decide
  have hdescent : baseEnd_2055548 < baseStart_2055548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055624 : List Nat := [2, 1, 3, 1, 3, 1, 1, 6, 3]
def baseStart_2055624 : Nat := 118140960795 + 2055624 * 2 ^ 59
def prefixEnd_2055624 : Nat := 4983230072969 + 3 ^ 40 * 2055624 * 2
def baseEnd_2055624 : Nat := 469121403074653597931717

theorem tailTrace_2055624 : CollatzResearch.WordTrace tailWord_2055624 prefixEnd_2055624 469121403074653597931717 := by
  unfold tailWord_2055624
  simp only [CollatzResearch.WordTrace]
  refine ⟨37487383352416397736994963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49983177803221863649326617 37487383352416397736994963)
  ·
    refine ⟨56231075028624596605492445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37487383352416397736994963 56231075028624596605492445)
    ·
      refine ⟨21086653135734223727059667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56231075028624596605492445 21086653135734223727059667)
      ·
        refine ⟨31629979703601335590589501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21086653135734223727059667 31629979703601335590589501)
        ·
          refine ⟨11861242388850500846471063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31629979703601335590589501 11861242388850500846471063)
          ·
            refine ⟨17791863583275751269706595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11861242388850500846471063 17791863583275751269706595)
            ·
              refine ⟨26687795374913626904559893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17791863583275751269706595 26687795374913626904559893)
              ·
                refine ⟨1250990408199076261151245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26687795374913626904559893 1250990408199076261151245)
                ·
                  refine ⟨469121403074653597931717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1250990408199076261151245 469121403074653597931717)
                  ·
                    rfl

theorem cell21_2055624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_2055624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055624 prefixEnd_2055624 := by exact prefixLift 2055624
  have htrace : WordTrace (prefixWord ++ tailWord_2055624) baseStart_2055624 baseEnd_2055624 := by
    simpa [prefixWord, tailWord_2055624, baseEnd_2055624] using wordTrace_append hprefix tailTrace_2055624
  have hstable : (prefixWord ++ tailWord_2055624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055624).length < 2 ^ (prefixWord ++ tailWord_2055624).sum := by decide
  have hdescent : baseEnd_2055624 < baseStart_2055624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055658 : List Nat := [3, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_2055658 : Nat := 118140960795 + 2055658 * 2 ^ 59
def prefixEnd_2055658 : Nat := 4983230072969 + 3 ^ 40 * 2055658 * 2
def baseEnd_2055658 : Nat := 469129162337877094364981

theorem tailTrace_2055658 : CollatzResearch.WordTrace tailWord_2055658 prefixEnd_2055658 469129162337877094364981 := by
  unfold tailWord_2055658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18744001696677404820181907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49984004524473079520485085 18744001696677404820181907)
  ·
    refine ⟨28116002545016107230272861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18744001696677404820181907 28116002545016107230272861)
    ·
      refine ⟨10543500954381040211352323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28116002545016107230272861 10543500954381040211352323)
      ·
        refine ⟨15815251431571560317028485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10543500954381040211352323 15815251431571560317028485)
        ·
          refine ⟨2965359643419667559442841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15815251431571560317028485 2965359643419667559442841)
          ·
            refine ⟨2224019732564750669582131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2965359643419667559442841 2224019732564750669582131)
            ·
              refine ⟨3336029598847126004373197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224019732564750669582131 3336029598847126004373197)
              ·
                refine ⟨1251011099567672251639949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3336029598847126004373197 1251011099567672251639949)
                ·
                  refine ⟨469129162337877094364981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251011099567672251639949 469129162337877094364981)
                  ·
                    rfl

theorem cell21_2055658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_2055658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055658 prefixEnd_2055658 := by exact prefixLift 2055658
  have htrace : WordTrace (prefixWord ++ tailWord_2055658) baseStart_2055658 baseEnd_2055658 := by
    simpa [prefixWord, tailWord_2055658, baseEnd_2055658] using wordTrace_append hprefix tailTrace_2055658
  have hstable : (prefixWord ++ tailWord_2055658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055658).length < 2 ^ (prefixWord ++ tailWord_2055658).sum := by decide
  have hdescent : baseEnd_2055658 < baseStart_2055658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055669 : List Nat := [1, 3, 5, 1, 1, 1, 9]
def baseStart_2055669 : Nat := 118140960795 + 2055669 * 2 ^ 59
def prefixEnd_2055669 : Nat := 4983230072969 + 3 ^ 40 * 2055669 * 2
def baseEnd_2055669 : Nat := 52125741409749279964625

theorem tailTrace_2055669 : CollatzResearch.WordTrace tailWord_2055669 prefixEnd_2055669 52125741409749279964625 := by
  unfold tailWord_2055669
  simp only [CollatzResearch.WordTrace]
  refine ⟨74976407989669768159378061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49984271993113178772918707 74976407989669768159378061)
  ·
    refine ⟨28116152996126163059766773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74976407989669768159378061 28116152996126163059766773)
    ·
      refine ⟨2635889343386827786853135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28116152996126163059766773 2635889343386827786853135)
      ·
        refine ⟨3953834015080241680279703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2635889343386827786853135 3953834015080241680279703)
        ·
          refine ⟨5930751022620362520419555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3953834015080241680279703 5930751022620362520419555)
          ·
            refine ⟨8896126533930543780629333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5930751022620362520419555 8896126533930543780629333)
            ·
              refine ⟨52125741409749279964625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8896126533930543780629333 52125741409749279964625)
              ·
                rfl

theorem cell21_2055669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 9].length) (baseStart_2055669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055669 prefixEnd_2055669 := by exact prefixLift 2055669
  have htrace : WordTrace (prefixWord ++ tailWord_2055669) baseStart_2055669 baseEnd_2055669 := by
    simpa [prefixWord, tailWord_2055669, baseEnd_2055669] using wordTrace_append hprefix tailTrace_2055669
  have hstable : (prefixWord ++ tailWord_2055669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055669).length < 2 ^ (prefixWord ++ tailWord_2055669).sum := by decide
  have hdescent : baseEnd_2055669 < baseStart_2055669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055734 : List Nat := [5, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_2055734 : Nat := 118140960795 + 2055734 * 2 ^ 59
def prefixEnd_2055734 : Nat := 4983230072969 + 3 ^ 40 * 2055734 * 2
def baseEnd_2055734 : Nat := 469146506573317851098159

theorem tailTrace_2055734 : CollatzResearch.WordTrace tailWord_2055734 prefixEnd_2055734 469146506573317851098159 := by
  unfold tailWord_2055734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686173670902142766280891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49985852489622856173662837 4686173670902142766280891)
  ·
    refine ⟨7029260506353214149421337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4686173670902142766280891 7029260506353214149421337)
    ·
      refine ⟨5271945379764910612066003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7029260506353214149421337 5271945379764910612066003)
      ·
        refine ⟨7907918069647365918099005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5271945379764910612066003 7907918069647365918099005)
        ·
          refine ⟨2965469276117762219287127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7907918069647365918099005 2965469276117762219287127)
          ·
            refine ⟨4448203914176643328930691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965469276117762219287127 4448203914176643328930691)
            ·
              refine ⟨6672305871264964993396037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448203914176643328930691 6672305871264964993396037)
              ·
                refine ⟨1251057350862180936261757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6672305871264964993396037 1251057350862180936261757)
                ·
                  refine ⟨469146506573317851098159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251057350862180936261757 469146506573317851098159)
                  ·
                    rfl

theorem cell21_2055734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_2055734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055734 prefixEnd_2055734 := by exact prefixLift 2055734
  have htrace : WordTrace (prefixWord ++ tailWord_2055734) baseStart_2055734 baseEnd_2055734 := by
    simpa [prefixWord, tailWord_2055734, baseEnd_2055734] using wordTrace_append hprefix tailTrace_2055734
  have hstable : (prefixWord ++ tailWord_2055734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055734).length < 2 ^ (prefixWord ++ tailWord_2055734).sum := by decide
  have hdescent : baseEnd_2055734 < baseStart_2055734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055866 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_2055866 : Nat := 118140960795 + 2055866 * 2 ^ 59
def prefixEnd_2055866 : Nat := 4983230072969 + 3 ^ 40 * 2055866 * 2
def baseEnd_2055866 : Nat := 469176630771714954897889

theorem tailTrace_2055866 : CollatzResearch.WordTrace tailWord_2055866 prefixEnd_2055866 469176630771714954897889 := by
  unfold tailWord_2055866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18745898292489017701074863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49989062113304047202866301 18745898292489017701074863)
  ·
    refine ⟨28118847438733526551612295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18745898292489017701074863 28118847438733526551612295)
    ·
      refine ⟨42178271158100289827418443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28118847438733526551612295 42178271158100289827418443)
      ·
        refine ⟨63267406737150434741127665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42178271158100289827418443 63267406737150434741127665)
        ·
          refine ⟨47450555052862826055845749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63267406737150434741127665 47450555052862826055845749)
          ·
            refine ⟨4448489536205889942735539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47450555052862826055845749 4448489536205889942735539)
            ·
              refine ⟨6672734304308834914103309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4448489536205889942735539 6672734304308834914103309)
              ·
                refine ⟨2502275364115813092788741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6672734304308834914103309 2502275364115813092788741)
                ·
                  refine ⟨469176630771714954897889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2502275364115813092788741 469176630771714954897889)
                  ·
                    rfl

theorem cell21_2055866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_2055866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055866 prefixEnd_2055866 := by exact prefixLift 2055866
  have htrace : WordTrace (prefixWord ++ tailWord_2055866) baseStart_2055866 baseEnd_2055866 := by
    simpa [prefixWord, tailWord_2055866, baseEnd_2055866] using wordTrace_append hprefix tailTrace_2055866
  have hstable : (prefixWord ++ tailWord_2055866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055866).length < 2 ^ (prefixWord ++ tailWord_2055866).sum := by decide
  have hdescent : baseEnd_2055866 < baseStart_2055866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055900 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_2055900 : Nat := 118140960795 + 2055900 * 2 ^ 59
def prefixEnd_2055900 : Nat := 4983230072969 + 3 ^ 40 * 2055900 * 2
def baseEnd_2055900 : Nat := 469184390034938451331153

theorem tailTrace_2055900 : CollatzResearch.WordTrace tailWord_2055900 prefixEnd_2055900 469184390034938451331153 := by
  unfold tailWord_2055900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37492416625916447305518577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49989888834555263074024769 37492416625916447305518577)
  ·
    refine ⟨28119312469437335479138933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37492416625916447305518577 28119312469437335479138933)
    ·
      refine ⟨2636185544009750201169275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28119312469437335479138933 2636185544009750201169275)
      ·
        refine ⟨3954278316014625301753913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636185544009750201169275 3954278316014625301753913)
        ·
          refine ⟨2965708737010968976315435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3954278316014625301753913 2965708737010968976315435)
          ·
            refine ⟨4448563105516453464473153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965708737010968976315435 4448563105516453464473153)
            ·
              refine ⟨3336422329137340098354865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448563105516453464473153 3336422329137340098354865)
              ·
                refine ⟨2502316746853005073766149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3336422329137340098354865 2502316746853005073766149)
                ·
                  refine ⟨469184390034938451331153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2502316746853005073766149 469184390034938451331153)
                  ·
                    rfl

theorem cell21_2055900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_2055900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055900 prefixEnd_2055900 := by exact prefixLift 2055900
  have htrace : WordTrace (prefixWord ++ tailWord_2055900) baseStart_2055900 baseEnd_2055900 := by
    simpa [prefixWord, tailWord_2055900, baseEnd_2055900] using wordTrace_append hprefix tailTrace_2055900
  have hstable : (prefixWord ++ tailWord_2055900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055900).length < 2 ^ (prefixWord ++ tailWord_2055900).sum := by decide
  have hdescent : baseEnd_2055900 < baseStart_2055900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055939 : List Nat := [1, 1, 1, 3, 2, 2, 2, 9]
def baseStart_2055939 : Nat := 118140960795 + 2055939 * 2 ^ 59
def prefixEnd_2055939 : Nat := 4983230072969 + 3 ^ 40 * 2055939 * 2
def baseEnd_2055939 : Nat := 156397763455427683393691

theorem tailTrace_2055939 : CollatzResearch.WordTrace tailWord_2055939 prefixEnd_2055939 156397763455427683393691 := by
  unfold tailWord_2055939
  simp only [CollatzResearch.WordTrace]
  refine ⟨74986255698691604271706871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49990837132461069514471247 74986255698691604271706871)
  ·
    refine ⟨112479383548037406407560307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74986255698691604271706871 112479383548037406407560307)
    ·
      refine ⟨168719075322056109611340461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112479383548037406407560307 168719075322056109611340461)
      ·
        refine ⟨63269653245771041104252673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168719075322056109611340461 63269653245771041104252673)
        ·
          refine ⟨47452239934328280828189505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63269653245771041104252673 47452239934328280828189505)
          ·
            refine ⟨35589179950746210621142129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47452239934328280828189505 35589179950746210621142129)
            ·
              refine ⟨26691884963059657965856597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35589179950746210621142129 26691884963059657965856597)
              ·
                refine ⟨156397763455427683393691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26691884963059657965856597 156397763455427683393691)
                ·
                  rfl

theorem cell21_2055939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 9].length) (baseStart_2055939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055939 prefixEnd_2055939 := by exact prefixLift 2055939
  have htrace : WordTrace (prefixWord ++ tailWord_2055939) baseStart_2055939 baseEnd_2055939 := by
    simpa [prefixWord, tailWord_2055939, baseEnd_2055939] using wordTrace_append hprefix tailTrace_2055939
  have hstable : (prefixWord ++ tailWord_2055939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055939).length < 2 ^ (prefixWord ++ tailWord_2055939).sum := by decide
  have hdescent : baseEnd_2055939 < baseStart_2055939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055959 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 4]
def baseStart_2055959 : Nat := 118140960795 + 2055959 * 2 ^ 59
def prefixEnd_2055959 : Nat := 4983230072969 + 3 ^ 40 * 2055959 * 2
def baseEnd_2055959 : Nat := 469197854638767459847699

theorem tailTrace_2055959 : CollatzResearch.WordTrace tailWord_2055959 prefixEnd_2055959 469197854638767459847699 := by
  unfold tailWord_2055959
  simp only [CollatzResearch.WordTrace]
  refine ⟨74986985158619147687434931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49991323439079431791623287 74986985158619147687434931)
  ·
    refine ⟨112480477737928721531152397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74986985158619147687434931 112480477737928721531152397)
    ·
      refine ⟨42180179151723270574182149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112480477737928721531152397 42180179151723270574182149)
      ·
        refine ⟨7908783590948113232659153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42180179151723270574182149 7908783590948113232659153)
        ·
          refine ⟨5931587693211084924494365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7908783590948113232659153 5931587693211084924494365)
          ·
            refine ⟨2224345384954156846685387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5931587693211084924494365 2224345384954156846685387)
            ·
              refine ⟨3336518077431235270028081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224345384954156846685387 3336518077431235270028081)
              ·
                refine ⟨2502388558073426452521061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3336518077431235270028081 2502388558073426452521061)
                ·
                  refine ⟨469197854638767459847699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2502388558073426452521061 469197854638767459847699)
                  ·
                    rfl

theorem cell21_2055959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 4].length) (baseStart_2055959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055959 prefixEnd_2055959 := by exact prefixLift 2055959
  have htrace : WordTrace (prefixWord ++ tailWord_2055959) baseStart_2055959 baseEnd_2055959 := by
    simpa [prefixWord, tailWord_2055959, baseEnd_2055959] using wordTrace_append hprefix tailTrace_2055959
  have hstable : (prefixWord ++ tailWord_2055959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055959).length < 2 ^ (prefixWord ++ tailWord_2055959).sum := by decide
  have hdescent : baseEnd_2055959 < baseStart_2055959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2055990 : List Nat := [5, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2055990 : Nat := 118140960795 + 2055990 * 2 ^ 59
def prefixEnd_2055990 : Nat := 4983230072969 + 3 ^ 40 * 2055990 * 2
def baseEnd_2055990 : Nat := 156401643087039431610323

theorem tailTrace_2055990 : CollatzResearch.WordTrace tailWord_2055990 prefixEnd_2055990 156401643087039431610323 := by
  unfold tailWord_2055990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4686757238844177498863339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49992077214337893321208949 4686757238844177498863339)
  ·
    refine ⟨7030135858266266248295009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4686757238844177498863339 7030135858266266248295009)
    ·
      refine ⟨5272601893699699686221257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7030135858266266248295009 5272601893699699686221257)
      ·
        refine ⟨3954451420274774764665943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5272601893699699686221257 3954451420274774764665943)
        ·
          refine ⟨5931677130412162146998915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954451420274774764665943 5931677130412162146998915)
          ·
            refine ⟨8897515695618243220498373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5931677130412162146998915 8897515695618243220498373)
            ·
              refine ⟨1668284192928420603843445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8897515695618243220498373 1668284192928420603843445)
              ·
                refine ⟨156401643087039431610323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1668284192928420603843445 156401643087039431610323)
                ·
                  rfl

theorem cell21_2055990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2055990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2055990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2055990 prefixEnd_2055990 := by exact prefixLift 2055990
  have htrace : WordTrace (prefixWord ++ tailWord_2055990) baseStart_2055990 baseEnd_2055990 := by
    simpa [prefixWord, tailWord_2055990, baseEnd_2055990] using wordTrace_append hprefix tailTrace_2055990
  have hstable : (prefixWord ++ tailWord_2055990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2055990).length < 2 ^ (prefixWord ++ tailWord_2055990).sum := by decide
  have hdescent : baseEnd_2055990 < baseStart_2055990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2055990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056021 : List Nat := [1, 3, 2, 2, 2, 3, 3, 2, 3]
def baseStart_2056021 : Nat := 118140960795 + 2056021 * 2 ^ 59
def prefixEnd_2056021 : Nat := 4983230072969 + 3 ^ 40 * 2056021 * 2
def baseEnd_2056021 : Nat := 469212003883469129814239

theorem tailTrace_2056021 : CollatzResearch.WordTrace tailWord_2056021 prefixEnd_2056021 469212003883469129814239 := by
  unfold tailWord_2056021
  simp only [CollatzResearch.WordTrace]
  refine ⟨74989246484394532276191917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49992830989596354850794611 74989246484394532276191917)
  ·
    refine ⟨28120967431647949603571969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74989246484394532276191917 28120967431647949603571969)
    ·
      refine ⟨21090725573735962202678977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28120967431647949603571969 21090725573735962202678977)
      ·
        refine ⟨15818044180301971652009233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21090725573735962202678977 15818044180301971652009233)
        ·
          refine ⟨11863533135226478739006925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15818044180301971652009233 11863533135226478739006925)
          ·
            refine ⟨4448824925709929527127597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11863533135226478739006925 4448824925709929527127597)
            ·
              refine ⟨1668309347141223572672849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4448824925709929527127597 1668309347141223572672849)
              ·
                refine ⟨1251232010355917679504637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668309347141223572672849 1251232010355917679504637)
                ·
                  refine ⟨469212003883469129814239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251232010355917679504637 469212003883469129814239)
                  ·
                    rfl

theorem cell21_2056021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_2056021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056021 prefixEnd_2056021 := by exact prefixLift 2056021
  have htrace : WordTrace (prefixWord ++ tailWord_2056021) baseStart_2056021 baseEnd_2056021 := by
    simpa [prefixWord, tailWord_2056021, baseEnd_2056021] using wordTrace_append hprefix tailTrace_2056021
  have hstable : (prefixWord ++ tailWord_2056021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056021).length < 2 ^ (prefixWord ++ tailWord_2056021).sum := by decide
  have hdescent : baseEnd_2056021 < baseStart_2056021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056032 : List Nat := [2, 1, 1, 3, 3, 3, 2, 6]
def baseStart_2056032 : Nat := 118140960795 + 2056032 * 2 ^ 59
def prefixEnd_2056032 : Nat := 4983230072969 + 3 ^ 40 * 2056032 * 2
def baseEnd_2056032 : Nat := 156404838077778518376961

theorem tailTrace_2056032 : CollatzResearch.WordTrace tailWord_2056032 prefixEnd_2056032 156404838077778518376961 := by
  unfold tailWord_2056032
  simp only [CollatzResearch.WordTrace]
  refine ⟨37494823843677340577421175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49993098458236454103228233 37494823843677340577421175)
  ·
    refine ⟨56242235765516010866131763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37494823843677340577421175 56242235765516010866131763)
    ·
      refine ⟨84363353648274016299197645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56242235765516010866131763 84363353648274016299197645)
      ·
        refine ⟨31636257618102756112199117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84363353648274016299197645 31636257618102756112199117)
        ·
          refine ⟨11863596606788533542074669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31636257618102756112199117 11863596606788533542074669)
          ·
            refine ⟨4448848727545700078278001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11863596606788533542074669 4448848727545700078278001)
            ·
              refine ⟨3336636545659275058708501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4448848727545700078278001 3336636545659275058708501)
              ·
                refine ⟨156404838077778518376961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3336636545659275058708501 156404838077778518376961)
                ·
                  rfl

theorem cell21_2056032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_2056032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056032 prefixEnd_2056032 := by exact prefixLift 2056032
  have htrace : WordTrace (prefixWord ++ tailWord_2056032) baseStart_2056032 baseEnd_2056032 := by
    simpa [prefixWord, tailWord_2056032, baseEnd_2056032] using wordTrace_append hprefix tailTrace_2056032
  have hstable : (prefixWord ++ tailWord_2056032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056032).length < 2 ^ (prefixWord ++ tailWord_2056032).sum := by decide
  have hdescent : baseEnd_2056032 < baseStart_2056032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056063 : List Nat := [1, 1, 2, 2, 1, 1, 3, 7, 3]
def baseStart_2056063 : Nat := 118140960795 + 2056063 * 2 ^ 59
def prefixEnd_2056063 : Nat := 4983230072969 + 3 ^ 40 * 2056063 * 2
def baseEnd_2056063 : Nat := 469221588855686390114153

theorem tailTrace_2056063 : CollatzResearch.WordTrace tailWord_2056063 prefixEnd_2056063 469221588855686390114153 := by
  unfold tailWord_2056063
  simp only [CollatzResearch.WordTrace]
  refine ⟨74990778350242373449220843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49993852233494915632813895 74990778350242373449220843)
  ·
    refine ⟨112486167525363560173831265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74990778350242373449220843 112486167525363560173831265)
    ·
      refine ⟨84364625644022670130373449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112486167525363560173831265 84364625644022670130373449)
      ·
        refine ⟨63273469233017002597780087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84364625644022670130373449 63273469233017002597780087)
        ·
          refine ⟨94910203849525503896670131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63273469233017002597780087 94910203849525503896670131)
          ·
            refine ⟨142365305774288255845005197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94910203849525503896670131 142365305774288255845005197)
            ·
              refine ⟨53386989665358095941876949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142365305774288255845005197 53386989665358095941876949)
              ·
                refine ⟨1251257570281830373637741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53386989665358095941876949 1251257570281830373637741)
                ·
                  refine ⟨469221588855686390114153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251257570281830373637741 469221588855686390114153)
                  ·
                    rfl

theorem cell21_2056063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 3].length) (baseStart_2056063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056063 prefixEnd_2056063 := by exact prefixLift 2056063
  have htrace : WordTrace (prefixWord ++ tailWord_2056063) baseStart_2056063 baseEnd_2056063 := by
    simpa [prefixWord, tailWord_2056063, baseEnd_2056063] using wordTrace_append hprefix tailTrace_2056063
  have hstable : (prefixWord ++ tailWord_2056063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056063).length < 2 ^ (prefixWord ++ tailWord_2056063).sum := by decide
  have hdescent : baseEnd_2056063 < baseStart_2056063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056139 : List Nat := [1, 1, 1, 1, 3, 4, 1, 6, 3]
def baseStart_2056139 : Nat := 118140960795 + 2056139 * 2 ^ 59
def prefixEnd_2056139 : Nat := 4983230072969 + 3 ^ 40 * 2056139 * 2
def baseEnd_2056139 : Nat := 469238933091127146847331

theorem tailTrace_2056139 : CollatzResearch.WordTrace tailWord_2056139 prefixEnd_2056139 469238933091127146847331 := by
  unfold tailWord_2056139
  simp only [CollatzResearch.WordTrace]
  refine ⟨74993550297967038428987471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49995700198644692285991647 74993550297967038428987471)
  ·
    refine ⟨112490325446950557643481207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74993550297967038428987471 112490325446950557643481207)
    ·
      refine ⟨168735488170425836465221811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112490325446950557643481207 168735488170425836465221811)
      ·
        refine ⟨253103232255638754697832717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168735488170425836465221811 253103232255638754697832717)
        ·
          refine ⟨94913712095864533011687269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253103232255638754697832717 94913712095864533011687269)
          ·
            refine ⟨17796321017974599939691363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94913712095864533011687269 17796321017974599939691363)
            ·
              refine ⟨26694481526961899909537045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17796321017974599939691363 26694481526961899909537045)
              ·
                refine ⟨1251303821576339058259549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26694481526961899909537045 1251303821576339058259549)
                ·
                  refine ⟨469238933091127146847331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251303821576339058259549 469238933091127146847331)
                  ·
                    rfl

theorem cell21_2056139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 3].length) (baseStart_2056139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056139 prefixEnd_2056139 := by exact prefixLift 2056139
  have htrace : WordTrace (prefixWord ++ tailWord_2056139) baseStart_2056139 baseEnd_2056139 := by
    simpa [prefixWord, tailWord_2056139, baseEnd_2056139] using wordTrace_append hprefix tailTrace_2056139
  have hstable : (prefixWord ++ tailWord_2056139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056139).length < 2 ^ (prefixWord ++ tailWord_2056139).sum := by decide
  have hdescent : baseEnd_2056139 < baseStart_2056139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056190 : List Nat := [4, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_2056190 : Nat := 118140960795 + 2056190 * 2 ^ 59
def prefixEnd_2056190 : Nat := 4983230072969 + 3 ^ 40 * 2056190 * 2
def baseEnd_2056190 : Nat := 469250571985962391497227

theorem tailTrace_2056190 : CollatzResearch.WordTrace tailWord_2056190 prefixEnd_2056190 469250571985962391497227 := by
  unfold tailWord_2056190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9374426302597784267386753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49996940280521516092729349 9374426302597784267386753)
  ·
    refine ⟨7030819726948338200540065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9374426302597784267386753 7030819726948338200540065)
    ·
      refine ⟨5273114795211253650405049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7030819726948338200540065 5273114795211253650405049)
      ·
        refine ⟨3954836096408440237803787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5273114795211253650405049 3954836096408440237803787)
        ·
          refine ⟨5932254144612660356705681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3954836096408440237803787 5932254144612660356705681)
          ·
            refine ⟨4449190608459495267529261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5932254144612660356705681 4449190608459495267529261)
            ·
              refine ⟨1668446478172310725323473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4449190608459495267529261 1668446478172310725323473)
              ·
                refine ⟨1251334858629233043992605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668446478172310725323473 1251334858629233043992605)
                ·
                  refine ⟨469250571985962391497227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251334858629233043992605 469250571985962391497227)
                  ·
                    rfl

theorem cell21_2056190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_2056190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056190 prefixEnd_2056190 := by exact prefixLift 2056190
  have htrace : WordTrace (prefixWord ++ tailWord_2056190) baseStart_2056190 baseEnd_2056190 := by
    simpa [prefixWord, tailWord_2056190, baseEnd_2056190] using wordTrace_append hprefix tailTrace_2056190
  have hstable : (prefixWord ++ tailWord_2056190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056190).length < 2 ^ (prefixWord ++ tailWord_2056190).sum := by decide
  have hdescent : baseEnd_2056190 < baseStart_2056190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056291 : List Nat := [1, 1, 1, 5, 1, 1, 3, 5, 3]
def baseStart_2056291 : Nat := 118140960795 + 2056291 * 2 ^ 59
def prefixEnd_2056291 : Nat := 4983230072969 + 3 ^ 40 * 2056291 * 2
def baseEnd_2056291 : Nat := 469273621562008660313687

theorem tailTrace_2056291 : CollatzResearch.WordTrace tailWord_2056291 prefixEnd_2056291 469273621562008660313687 := by
  unfold tailWord_2056291
  simp only [CollatzResearch.WordTrace]
  refine ⟨74999094193416368388520727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49999396128944245592347151 74999094193416368388520727)
  ·
    refine ⟨112498641290124552582781091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74999094193416368388520727 112498641290124552582781091)
    ·
      refine ⟨168747961935186828874171637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112498641290124552582781091 168747961935186828874171637)
      ·
        refine ⟨15820121431423765206953591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168747961935186828874171637 15820121431423765206953591)
        ·
          refine ⟨23730182147135647810430387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15820121431423765206953591 23730182147135647810430387)
          ·
            refine ⟨35595273220703471715645581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23730182147135647810430387 35595273220703471715645581)
            ·
              refine ⟨13348227457763801893367093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35595273220703471715645581 13348227457763801893367093)
              ·
                refine ⟨1251396324165356427503165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13348227457763801893367093 1251396324165356427503165)
                ·
                  refine ⟨469273621562008660313687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251396324165356427503165 469273621562008660313687)
                  ·
                    rfl

theorem cell21_2056291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 3].length) (baseStart_2056291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056291 prefixEnd_2056291 := by exact prefixLift 2056291
  have htrace : WordTrace (prefixWord ++ tailWord_2056291) baseStart_2056291 baseEnd_2056291 := by
    simpa [prefixWord, tailWord_2056291, baseEnd_2056291] using wordTrace_append hprefix tailTrace_2056291
  have hstable : (prefixWord ++ tailWord_2056291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056291).length < 2 ^ (prefixWord ++ tailWord_2056291).sum := by decide
  have hdescent : baseEnd_2056291 < baseStart_2056291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056373 : List Nat := [1, 3, 3, 4, 2, 1, 2, 1, 4]
def baseStart_2056373 : Nat := 118140960795 + 2056373 * 2 ^ 59
def prefixEnd_2056373 : Nat := 4983230072969 + 3 ^ 40 * 2056373 * 2
def baseEnd_2056373 : Nat := 469292335079194739946853

theorem tailTrace_2056373 : CollatzResearch.WordTrace tailWord_2056373 prefixEnd_2056373 469292335079194739946853 := by
  unfold tailWord_2056373
  simp only [CollatzResearch.WordTrace]
  refine ⟨75002084979119296393005773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50001389986079530928670515 75002084979119296393005773)
  ·
    refine ⟨28125781867169736147377165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75002084979119296393005773 28125781867169736147377165)
    ·
      refine ⟨10547168200188651055266437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28125781867169736147377165 10547168200188651055266437)
      ·
        refine ⟨1977594037535372072862457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10547168200188651055266437 1977594037535372072862457)
        ·
          refine ⟨1483195528151529054646843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1977594037535372072862457 1483195528151529054646843)
          ·
            refine ⟨2224793292227293581970265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483195528151529054646843 2224793292227293581970265)
            ·
              refine ⟨1668594969170470186477699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224793292227293581970265 1668594969170470186477699)
              ·
                refine ⟨2502892453755705279716549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1668594969170470186477699 2502892453755705279716549)
                ·
                  refine ⟨469292335079194739946853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2502892453755705279716549 469292335079194739946853)
                  ·
                    rfl

theorem cell21_2056373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_2056373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056373 prefixEnd_2056373 := by exact prefixLift 2056373
  have htrace : WordTrace (prefixWord ++ tailWord_2056373) baseStart_2056373 baseEnd_2056373 := by
    simpa [prefixWord, tailWord_2056373, baseEnd_2056373] using wordTrace_append hprefix tailTrace_2056373
  have hstable : (prefixWord ++ tailWord_2056373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056373).length < 2 ^ (prefixWord ++ tailWord_2056373).sum := by decide
  have hdescent : baseEnd_2056373 < baseStart_2056373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056412 : List Nat := [2, 2, 5, 2, 10]
def baseStart_2056412 : Nat := 118140960795 + 2056412 * 2 ^ 59
def prefixEnd_2056412 : Nat := 4983230072969 + 3 ^ 40 * 2056412 * 2
def baseEnd_2056412 : Nat := 5793842412475794306133

theorem tailTrace_2056412 : CollatzResearch.WordTrace tailWord_2056412 prefixEnd_2056412 5793842412475794306133 := by
  unfold tailWord_2056412
  simp only [CollatzResearch.WordTrace]
  refine ⟨37501753712989003026837745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50002338283985337369116993 37501753712989003026837745)
  ·
    refine ⟨28126315284741752270128309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37501753712989003026837745 28126315284741752270128309)
    ·
      refine ⟨2636842057944539275324529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28126315284741752270128309 2636842057944539275324529)
      ·
        refine ⟨1977631543458404456493397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2636842057944539275324529 1977631543458404456493397)
        ·
          refine ⟨5793842412475794306133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1977631543458404456493397 5793842412475794306133)
          ·
            rfl

theorem cell21_2056412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 10].length) (baseStart_2056412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056412 prefixEnd_2056412 := by exact prefixLift 2056412
  have htrace : WordTrace (prefixWord ++ tailWord_2056412) baseStart_2056412 baseEnd_2056412 := by
    simpa [prefixWord, tailWord_2056412, baseEnd_2056412] using wordTrace_append hprefix tailTrace_2056412
  have hstable : (prefixWord ++ tailWord_2056412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056412).length < 2 ^ (prefixWord ++ tailWord_2056412).sum := by decide
  have hdescent : baseEnd_2056412 < baseStart_2056412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056426 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_2056426 : Nat := 118140960795 + 2056426 * 2 ^ 59
def prefixEnd_2056426 : Nat := 4983230072969 + 3 ^ 40 * 2056426 * 2
def baseEnd_2056426 : Nat := 469304430401278425563411

theorem tailTrace_2056426 : CollatzResearch.WordTrace tailWord_2056426 prefixEnd_2056426 469304430401278425563411 := by
  unfold tailWord_2056426
  simp only [CollatzResearch.WordTrace]
  refine ⟨18751004511981821611171283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50002678698618190963123421 18751004511981821611171283)
  ·
    refine ⟨28126506767972732416756925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18751004511981821611171283 28126506767972732416756925)
    ·
      refine ⟨10547440037989774656283847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28126506767972732416756925 10547440037989774656283847)
      ·
        refine ⟨15821160056984661984425771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10547440037989774656283847 15821160056984661984425771)
        ·
          refine ⟨23731740085476992976638657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15821160056984661984425771 23731740085476992976638657)
          ·
            refine ⟨17798805064107744732478993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23731740085476992976638657 17798805064107744732478993)
            ·
              refine ⟨13349103798080808549359245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17798805064107744732478993 13349103798080808549359245)
              ·
                refine ⟨5005913924280303206009717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13349103798080808549359245 5005913924280303206009717)
                ·
                  refine ⟨469304430401278425563411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5005913924280303206009717 469304430401278425563411)
                  ·
                    rfl

theorem cell21_2056426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_2056426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056426 prefixEnd_2056426 := by exact prefixLift 2056426
  have htrace : WordTrace (prefixWord ++ tailWord_2056426) baseStart_2056426 baseEnd_2056426 := by
    simpa [prefixWord, tailWord_2056426, baseEnd_2056426] using wordTrace_append hprefix tailTrace_2056426
  have hstable : (prefixWord ++ tailWord_2056426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056426).length < 2 ^ (prefixWord ++ tailWord_2056426).sum := by decide
  have hdescent : baseEnd_2056426 < baseStart_2056426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056429 : List Nat := [1, 5, 1, 2, 3, 2, 1, 6]
def baseStart_2056429 : Nat := 118140960795 + 2056429 * 2 ^ 59
def prefixEnd_2056429 : Nat := 4983230072969 + 3 ^ 40 * 2056429 * 2
def baseEnd_2056429 : Nat := 156435038347383695671135

theorem tailTrace_2056429 : CollatzResearch.WordTrace tailWord_2056429 prefixEnd_2056429 156435038347383695671135 := by
  unfold tailWord_2056429
  simp only [CollatzResearch.WordTrace]
  refine ⟨75004127466916417957044341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50002751644610945304696227 75004127466916417957044341)
  ·
    refine ⟨7031636950023414183472907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75004127466916417957044341 7031636950023414183472907)
    ·
      refine ⟨10547455425035121275209361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7031636950023414183472907 10547455425035121275209361)
      ·
        refine ⟨7910591568776340956407021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10547455425035121275209361 7910591568776340956407021)
        ·
          refine ⟨2966471838291127858652633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7910591568776340956407021 2966471838291127858652633)
          ·
            refine ⟨2224853878718345893989475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2966471838291127858652633 2224853878718345893989475)
            ·
              refine ⟨3337280818077518840984213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2224853878718345893989475 3337280818077518840984213)
              ·
                refine ⟨156435038347383695671135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3337280818077518840984213 156435038347383695671135)
                ·
                  rfl

theorem cell21_2056429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 6].length) (baseStart_2056429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056429 prefixEnd_2056429 := by exact prefixLift 2056429
  have htrace : WordTrace (prefixWord ++ tailWord_2056429) baseStart_2056429 baseEnd_2056429 := by
    simpa [prefixWord, tailWord_2056429, baseEnd_2056429] using wordTrace_append hprefix tailTrace_2056429
  have hstable : (prefixWord ++ tailWord_2056429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056429).length < 2 ^ (prefixWord ++ tailWord_2056429).sum := by decide
  have hdescent : baseEnd_2056429 < baseStart_2056429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056471 : List Nat := [1, 1, 3, 4, 1, 3, 8]
def baseStart_2056471 : Nat := 118140960795 + 2056471 * 2 ^ 59
def prefixEnd_2056471 : Nat := 4983230072969 + 3 ^ 40 * 2056471 * 2
def baseEnd_2056471 : Nat := 52146077779374260812591

theorem tailTrace_2056471 : CollatzResearch.WordTrace tailWord_2056471 prefixEnd_2056471 52146077779374260812591 := by
  unfold tailWord_2056471
  simp only [CollatzResearch.WordTrace]
  refine ⟨75005659332764259130073267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50003772888509506086715511 75005659332764259130073267)
  ·
    refine ⟨112508488999146388695109901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75005659332764259130073267 112508488999146388695109901)
    ·
      refine ⟨42190683374679895760666213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112508488999146388695109901 42190683374679895760666213)
      ·
        refine ⟨7910753132752480455124915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42190683374679895760666213 7910753132752480455124915)
        ·
          refine ⟨11866129699128720682687373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7910753132752480455124915 11866129699128720682687373)
          ·
            refine ⟨4449798637173270256007765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11866129699128720682687373 4449798637173270256007765)
            ·
              refine ⟨52146077779374260812591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4449798637173270256007765 52146077779374260812591)
              ·
                rfl

theorem cell21_2056471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 8].length) (baseStart_2056471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056471 prefixEnd_2056471 := by exact prefixLift 2056471
  have htrace : WordTrace (prefixWord ++ tailWord_2056471) baseStart_2056471 baseEnd_2056471 := by
    simpa [prefixWord, tailWord_2056471, baseEnd_2056471] using wordTrace_append hprefix tailTrace_2056471
  have hstable : (prefixWord ++ tailWord_2056471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056471).length < 2 ^ (prefixWord ++ tailWord_2056471).sum := by decide
  have hdescent : baseEnd_2056471 < baseStart_2056471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056505 : List Nat := [1, 2, 1, 6, 1, 3, 2, 5]
def baseStart_2056505 : Nat := 118140960795 + 2056505 * 2 ^ 59
def prefixEnd_2056505 : Nat := 4983230072969 + 3 ^ 40 * 2056505 * 2
def baseEnd_2056505 : Nat := 156440819759197281248861

theorem tailTrace_2056505 : CollatzResearch.WordTrace tailWord_2056505 prefixEnd_2056505 156440819759197281248861 := by
  unfold tailWord_2056505
  simp only [CollatzResearch.WordTrace]
  refine ⟨75006899414641082936810969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50004599609760721957873979 75006899414641082936810969)
  ·
    refine ⟨56255174560980812202608227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75006899414641082936810969 56255174560980812202608227)
    ·
      refine ⟨84382761841471218303912341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56255174560980812202608227 84382761841471218303912341)
      ·
        refine ⟨3955441961318963357995891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84382761841471218303912341 3955441961318963357995891)
        ·
          refine ⟨5933162941978445036993837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955441961318963357995891 5933162941978445036993837)
          ·
            refine ⟨2224936103241916888872689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5933162941978445036993837 2224936103241916888872689)
            ·
              refine ⟨1668702077431437666654517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2224936103241916888872689 1668702077431437666654517)
              ·
                refine ⟨156440819759197281248861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1668702077431437666654517 156440819759197281248861)
                ·
                  rfl

theorem cell21_2056505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 5].length) (baseStart_2056505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056505 prefixEnd_2056505 := by exact prefixLift 2056505
  have htrace : WordTrace (prefixWord ++ tailWord_2056505) baseStart_2056505 baseEnd_2056505 := by
    simpa [prefixWord, tailWord_2056505, baseEnd_2056505] using wordTrace_append hprefix tailTrace_2056505
  have hstable : (prefixWord ++ tailWord_2056505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056505).length < 2 ^ (prefixWord ++ tailWord_2056505).sum := by decide
  have hdescent : baseEnd_2056505 < baseStart_2056505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056547 : List Nat := [1, 1, 1, 5, 2, 1, 4, 6]
def baseStart_2056547 : Nat := 118140960795 + 2056547 * 2 ^ 59
def prefixEnd_2056547 : Nat := 4983230072969 + 3 ^ 40 * 2056547 * 2
def baseEnd_2056547 : Nat := 156444014749936368015499

theorem tailTrace_2056547 : CollatzResearch.WordTrace tailWord_2056547 prefixEnd_2056547 156444014749936368015499 := by
  unfold tailWord_2056547
  simp only [CollatzResearch.WordTrace]
  refine ⟨75008431280488924109839895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50005620853659282739893263 75008431280488924109839895)
  ·
    refine ⟨112512646920733386164759843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75008431280488924109839895 112512646920733386164759843)
    ·
      refine ⟨168768970381100079247139765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112512646920733386164759843 168768970381100079247139765)
      ·
        refine ⟨15822090973228132429419353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168768970381100079247139765 15822090973228132429419353)
        ·
          refine ⟨11866568229921099322064515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15822090973228132429419353 11866568229921099322064515)
          ·
            refine ⟨17799852344881648983096773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11866568229921099322064515 17799852344881648983096773)
            ·
              refine ⟨3337472314665309184330645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17799852344881648983096773 3337472314665309184330645)
              ·
                refine ⟨156444014749936368015499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3337472314665309184330645 156444014749936368015499)
                ·
                  rfl

theorem cell21_2056547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 6].length) (baseStart_2056547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056547 prefixEnd_2056547 := by exact prefixLift 2056547
  have htrace : WordTrace (prefixWord ++ tailWord_2056547) baseStart_2056547 baseEnd_2056547 := by
    simpa [prefixWord, tailWord_2056547, baseEnd_2056547] using wordTrace_append hprefix tailTrace_2056547
  have hstable : (prefixWord ++ tailWord_2056547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056547).length < 2 ^ (prefixWord ++ tailWord_2056547).sum := by decide
  have hdescent : baseEnd_2056547 < baseStart_2056547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056561 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 7]
def baseStart_2056561 : Nat := 118140960795 + 2056561 * 2 ^ 59
def prefixEnd_2056561 : Nat := 4983230072969 + 3 ^ 40 * 2056561 * 2
def baseEnd_2056561 : Nat := 469335239240548190813135

theorem tailTrace_2056561 : CollatzResearch.WordTrace tailWord_2056561 prefixEnd_2056561 469335239240548190813135 := by
  unfold tailWord_2056561
  simp only [CollatzResearch.WordTrace]
  refine ⟨75008941902438204500849537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50005961268292136333899691 75008941902438204500849537)
  ·
    refine ⟨56256706426828653375637153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75008941902438204500849537 56256706426828653375637153)
    ·
      refine ⟨42192529820121490031727865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56256706426828653375637153 42192529820121490031727865)
      ·
        refine ⟨31644397365091117523795899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42192529820121490031727865 31644397365091117523795899)
        ·
          refine ⟨47466596047636676285693849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31644397365091117523795899 47466596047636676285693849)
          ·
            refine ⟨35599947035727507214270387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47466596047636676285693849 35599947035727507214270387)
            ·
              refine ⟨53399920553591260821405581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35599947035727507214270387 53399920553591260821405581)
              ·
                refine ⟨20024970207596722808027093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53399920553591260821405581 20024970207596722808027093)
                ·
                  refine ⟨469335239240548190813135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20024970207596722808027093 469335239240548190813135)
                  ·
                    rfl

theorem cell21_2056561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_2056561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056561 prefixEnd_2056561 := by exact prefixLift 2056561
  have htrace : WordTrace (prefixWord ++ tailWord_2056561) baseStart_2056561 baseEnd_2056561 := by
    simpa [prefixWord, tailWord_2056561, baseEnd_2056561] using wordTrace_append hprefix tailTrace_2056561
  have hstable : (prefixWord ++ tailWord_2056561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056561).length < 2 ^ (prefixWord ++ tailWord_2056561).sum := by decide
  have hdescent : baseEnd_2056561 < baseStart_2056561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056685 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2056685 : Nat := 118140960795 + 2056685 * 2 ^ 59
def prefixEnd_2056685 : Nat := 4983230072969 + 3 ^ 40 * 2056685 * 2
def baseEnd_2056685 : Nat := 469363537729951530746215

theorem tailTrace_2056685 : CollatzResearch.WordTrace tailWord_2056685 prefixEnd_2056685 469363537729951530746215 := by
  unfold tailWord_2056685
  simp only [CollatzResearch.WordTrace]
  refine ⟨75013464553988973678363509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50008976369325982452242339 75013464553988973678363509)
  ·
    refine ⟨7032512301936466282346579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75013464553988973678363509 7032512301936466282346579)
    ·
      refine ⟨10548768452904699423519869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7032512301936466282346579 10548768452904699423519869)
      ·
        refine ⟨3955788169839262283819951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10548768452904699423519869 3955788169839262283819951)
        ·
          refine ⟨5933682254758893425729927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3955788169839262283819951 5933682254758893425729927)
          ·
            refine ⟨8900523382138340138594891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933682254758893425729927 8900523382138340138594891)
            ·
              refine ⟨13350785073207510207892337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8900523382138340138594891 13350785073207510207892337)
              ·
                refine ⟨10013088804905632655919253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13350785073207510207892337 10013088804905632655919253)
                ·
                  refine ⟨469363537729951530746215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10013088804905632655919253 469363537729951530746215)
                  ·
                    rfl

theorem cell21_2056685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2056685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056685 prefixEnd_2056685 := by exact prefixLift 2056685
  have htrace : WordTrace (prefixWord ++ tailWord_2056685) baseStart_2056685 baseEnd_2056685 := by
    simpa [prefixWord, tailWord_2056685, baseEnd_2056685] using wordTrace_append hprefix tailTrace_2056685
  have hstable : (prefixWord ++ tailWord_2056685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056685).length < 2 ^ (prefixWord ++ tailWord_2056685).sum := by decide
  have hdescent : baseEnd_2056685 < baseStart_2056685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056713 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 5]
def baseStart_2056713 : Nat := 118140960795 + 2056713 * 2 ^ 59
def prefixEnd_2056713 : Nat := 4983230072969 + 3 ^ 40 * 2056713 * 2
def baseEnd_2056713 : Nat := 469369927711429704279491

theorem tailTrace_2056713 : CollatzResearch.WordTrace tailWord_2056713 prefixEnd_2056713 469369927711429704279491 := by
  unfold tailWord_2056713
  simp only [CollatzResearch.WordTrace]
  refine ⟨75014485797887534460382793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50009657198591689640255195 75014485797887534460382793)
  ·
    refine ⟨56260864348415650845287095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75014485797887534460382793 56260864348415650845287095)
    ·
      refine ⟨84391296522623476267930643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56260864348415650845287095 84391296522623476267930643)
      ·
        refine ⟨126586944783935214401895965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84391296522623476267930643 126586944783935214401895965)
        ·
          refine ⟨47470104293975705400710987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126586944783935214401895965 47470104293975705400710987)
          ·
            refine ⟨71205156440963558101066481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47470104293975705400710987 71205156440963558101066481)
            ·
              refine ⟨53403867330722668575799861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71205156440963558101066481 53403867330722668575799861)
              ·
                refine ⟨5006612562255250178981237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53403867330722668575799861 5006612562255250178981237)
                ·
                  refine ⟨469369927711429704279491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5006612562255250178981237 469369927711429704279491)
                  ·
                    rfl

theorem cell21_2056713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_2056713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056713 prefixEnd_2056713 := by exact prefixLift 2056713
  have htrace : WordTrace (prefixWord ++ tailWord_2056713) baseStart_2056713 baseEnd_2056713 := by
    simpa [prefixWord, tailWord_2056713, baseEnd_2056713] using wordTrace_append hprefix tailTrace_2056713
  have hstable : (prefixWord ++ tailWord_2056713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056713).length < 2 ^ (prefixWord ++ tailWord_2056713).sum := by decide
  have hdescent : baseEnd_2056713 < baseStart_2056713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056761 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 4]
def baseStart_2056761 : Nat := 118140960795 + 2056761 * 2 ^ 59
def prefixEnd_2056761 : Nat := 4983230072969 + 3 ^ 40 * 2056761 * 2
def baseEnd_2056761 : Nat := 469380881965392287479393

theorem tailTrace_2056761 : CollatzResearch.WordTrace tailWord_2056761 prefixEnd_2056761 469380881965392287479393 := by
  unfold tailWord_2056761
  simp only [CollatzResearch.WordTrace]
  refine ⟨75016236501713638658130137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50010824334475759105420091 75016236501713638658130137)
  ·
    refine ⟨56262177376285228993597603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75016236501713638658130137 56262177376285228993597603)
    ·
      refine ⟨84393266064427843490396405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56262177376285228993597603 84393266064427843490396405)
      ·
        refine ⟨7911868693540110327224663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84393266064427843490396405 7911868693540110327224663)
        ·
          refine ⟨11867803040310165490836995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7911868693540110327224663 11867803040310165490836995)
          ·
            refine ⟨17801704560465248236255493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11867803040310165490836995 17801704560465248236255493)
            ·
              refine ⟨3337819605087234044297905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17801704560465248236255493 3337819605087234044297905)
              ·
                refine ⟨2503364703815425533223429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3337819605087234044297905 2503364703815425533223429)
                ·
                  refine ⟨469380881965392287479393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2503364703815425533223429 469380881965392287479393)
                  ·
                    rfl

theorem cell21_2056761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_2056761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056761 prefixEnd_2056761 := by exact prefixLift 2056761
  have htrace : WordTrace (prefixWord ++ tailWord_2056761) baseStart_2056761 baseEnd_2056761 := by
    simpa [prefixWord, tailWord_2056761, baseEnd_2056761] using wordTrace_append hprefix tailTrace_2056761
  have hstable : (prefixWord ++ tailWord_2056761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056761).length < 2 ^ (prefixWord ++ tailWord_2056761).sum := by decide
  have hdescent : baseEnd_2056761 < baseStart_2056761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056764 : List Nat := [2, 2, 2, 2, 3, 1, 4, 2, 3]
def baseStart_2056764 : Nat := 118140960795 + 2056764 * 2 ^ 59
def prefixEnd_2056764 : Nat := 4983230072969 + 3 ^ 40 * 2056764 * 2
def baseEnd_2056764 : Nat := 469381566606264948929387

theorem tailTrace_2056764 : CollatzResearch.WordTrace tailWord_2056764 prefixEnd_2056764 469381566606264948929387 := by
  unfold tailWord_2056764
  simp only [CollatzResearch.WordTrace]
  refine ⟨37508172960351385085244673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50010897280468513446992897 37508172960351385085244673)
  ·
    refine ⟨28131129720263538813933505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37508172960351385085244673 28131129720263538813933505)
    ·
      refine ⟨21098347290197654110450129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28131129720263538813933505 21098347290197654110450129)
      ·
        refine ⟨15823760467648240582837597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21098347290197654110450129 15823760467648240582837597)
        ·
          refine ⟨5933910175368090218564099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15823760467648240582837597 5933910175368090218564099)
          ·
            refine ⟨8900865263052135327846149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933910175368090218564099 8900865263052135327846149)
            ·
              refine ⟨1668912236822275373971153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8900865263052135327846149 1668912236822275373971153)
              ·
                refine ⟨1251684177616706530478365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1668912236822275373971153 1251684177616706530478365)
                ·
                  refine ⟨469381566606264948929387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251684177616706530478365 469381566606264948929387)
                  ·
                    rfl

theorem cell21_2056764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_2056764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056764 prefixEnd_2056764 := by exact prefixLift 2056764
  have htrace : WordTrace (prefixWord ++ tailWord_2056764) baseStart_2056764 baseEnd_2056764 := by
    simpa [prefixWord, tailWord_2056764, baseEnd_2056764] using wordTrace_append hprefix tailTrace_2056764
  have hstable : (prefixWord ++ tailWord_2056764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056764).length < 2 ^ (prefixWord ++ tailWord_2056764).sum := by decide
  have hdescent : baseEnd_2056764 < baseStart_2056764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056775 : List Nat := [1, 1, 4, 1, 4, 1, 3, 6]
def baseStart_2056775 : Nat := 118140960795 + 2056775 * 2 ^ 59
def prefixEnd_2056775 : Nat := 4983230072969 + 3 ^ 40 * 2056775 * 2
def baseEnd_2056775 : Nat := 156461358985377124748677

theorem tailTrace_2056775 : CollatzResearch.WordTrace tailWord_2056775 prefixEnd_2056775 156461358985377124748677 := by
  unfold tailWord_2056775
  simp only [CollatzResearch.WordTrace]
  refine ⟨75016747123662919049139779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50011164749108612699426519 75016747123662919049139779)
  ·
    refine ⟨112525120685494378573709669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75016747123662919049139779 112525120685494378573709669)
    ·
      refine ⟨21098460128530195982570563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112525120685494378573709669 21098460128530195982570563)
      ·
        refine ⟨31647690192795293973855845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21098460128530195982570563 31647690192795293973855845)
        ·
          refine ⟨5933941911149117620097971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31647690192795293973855845 5933941911149117620097971)
          ·
            refine ⟨8900912866723676430146957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5933941911149117620097971 8900912866723676430146957)
            ·
              refine ⟨3337842325021378661305109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8900912866723676430146957 3337842325021378661305109)
              ·
                refine ⟨156461358985377124748677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3337842325021378661305109 156461358985377124748677)
                ·
                  rfl

theorem cell21_2056775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 6].length) (baseStart_2056775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056775 prefixEnd_2056775 := by exact prefixLift 2056775
  have htrace : WordTrace (prefixWord ++ tailWord_2056775) baseStart_2056775 baseEnd_2056775 := by
    simpa [prefixWord, tailWord_2056775, baseEnd_2056775] using wordTrace_append hprefix tailTrace_2056775
  have hstable : (prefixWord ++ tailWord_2056775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056775).length < 2 ^ (prefixWord ++ tailWord_2056775).sum := by decide
  have hdescent : baseEnd_2056775 < baseStart_2056775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056789 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 7]
def baseStart_2056789 : Nat := 118140960795 + 2056789 * 2 ^ 59
def prefixEnd_2056789 : Nat := 4983230072969 + 3 ^ 40 * 2056789 * 2
def baseEnd_2056789 : Nat := 469387271946870461012669

theorem tailTrace_2056789 : CollatzResearch.WordTrace tailWord_2056789 prefixEnd_2056789 469387271946870461012669 := by
  unfold tailWord_2056789
  simp only [CollatzResearch.WordTrace]
  refine ⟨75017257745612199440149421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50011505163741466293432947 75017257745612199440149421)
  ·
    refine ⟨28131471654604574790056033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75017257745612199440149421 28131471654604574790056033)
    ·
      refine ⟨21098603740953431092542025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28131471654604574790056033 21098603740953431092542025)
      ·
        refine ⟨15823952805715073319406519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21098603740953431092542025 15823952805715073319406519)
        ·
          refine ⟨23735929208572609979109779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15823952805715073319406519 23735929208572609979109779)
          ·
            refine ⟨35603893812858914968664669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23735929208572609979109779 35603893812858914968664669)
            ·
              refine ⟨13351460179822093113249251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35603893812858914968664669 13351460179822093113249251)
              ·
                refine ⟨20027190269733139669873877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13351460179822093113249251 20027190269733139669873877)
                ·
                  refine ⟨469387271946870461012669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20027190269733139669873877 469387271946870461012669)
                  ·
                    rfl

theorem cell21_2056789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_2056789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056789 prefixEnd_2056789 := by exact prefixLift 2056789
  have htrace : WordTrace (prefixWord ++ tailWord_2056789) baseStart_2056789 baseEnd_2056789 := by
    simpa [prefixWord, tailWord_2056789, baseEnd_2056789] using wordTrace_append hprefix tailTrace_2056789
  have hstable : (prefixWord ++ tailWord_2056789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056789).length < 2 ^ (prefixWord ++ tailWord_2056789).sum := by decide
  have hdescent : baseEnd_2056789 < baseStart_2056789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056874 : List Nat := [3, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_2056874 : Nat := 118140960795 + 2056874 * 2 ^ 59
def prefixEnd_2056874 : Nat := 4983230072969 + 3 ^ 40 * 2056874 * 2
def baseEnd_2056874 : Nat := 469406670104929202095829

theorem tailTrace_2056874 : CollatzResearch.WordTrace tailWord_2056874 prefixEnd_2056874 469406670104929202095829 := by
  unfold tailWord_2056874
  simp only [CollatzResearch.WordTrace]
  refine ⟨18755089487576064739248419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50013571966869505971329117 18755089487576064739248419)
  ·
    refine ⟨28132634231364097108872629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18755089487576064739248419 28132634231364097108872629)
    ·
      refine ⟨2637434459190384103956809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28132634231364097108872629 2637434459190384103956809)
      ·
        refine ⟨1978075844392788077967607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2637434459190384103956809 1978075844392788077967607)
        ·
          refine ⟨2967113766589182116951411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978075844392788077967607 2967113766589182116951411)
          ·
            refine ⟨4450670649883773175427117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967113766589182116951411 4450670649883773175427117)
            ·
              refine ⟨1669001493706414940785169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4450670649883773175427117 1669001493706414940785169)
              ·
                refine ⟨1251751120279811205588877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669001493706414940785169 1251751120279811205588877)
                ·
                  refine ⟨469406670104929202095829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251751120279811205588877 469406670104929202095829)
                  ·
                    rfl

theorem cell21_2056874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_2056874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056874 prefixEnd_2056874 := by exact prefixLift 2056874
  have htrace : WordTrace (prefixWord ++ tailWord_2056874) baseStart_2056874 baseEnd_2056874 := by
    simpa [prefixWord, tailWord_2056874, baseEnd_2056874] using wordTrace_append hprefix tailTrace_2056874
  have hstable : (prefixWord ++ tailWord_2056874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056874).length < 2 ^ (prefixWord ++ tailWord_2056874).sum := by decide
  have hdescent : baseEnd_2056874 < baseStart_2056874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056958 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_2056958 : Nat := 118140960795 + 2056958 * 2 ^ 59
def prefixEnd_2056958 : Nat := 4983230072969 + 3 ^ 40 * 2056958 * 2
def baseEnd_2056958 : Nat := 469425840049363722695657

theorem tailTrace_2056958 : CollatzResearch.WordTrace tailWord_2056958 prefixEnd_2056958 469425840049363722695657 := by
  unfold tailWord_2056958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9377927710249992662881441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50015614454666627535367685 9377927710249992662881441)
  ·
    refine ⟨7033445782687494497161081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9377927710249992662881441 7033445782687494497161081)
    ·
      refine ⟨5275084337015620872870811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7033445782687494497161081 5275084337015620872870811)
      ·
        refine ⟨7912626505523431309306217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275084337015620872870811 7912626505523431309306217)
        ·
          refine ⟨5934469879142573481979663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7912626505523431309306217 5934469879142573481979663)
          ·
            refine ⟨8901704818713860222969495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5934469879142573481979663 8901704818713860222969495)
            ·
              refine ⟨13352557228070790334454243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8901704818713860222969495 13352557228070790334454243)
              ·
                refine ⟨20028835842106185501681365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13352557228070790334454243 20028835842106185501681365)
                ·
                  refine ⟨469425840049363722695657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20028835842106185501681365 469425840049363722695657)
                  ·
                    rfl

theorem cell21_2056958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_2056958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056958 prefixEnd_2056958 := by exact prefixLift 2056958
  have htrace : WordTrace (prefixWord ++ tailWord_2056958) baseStart_2056958 baseEnd_2056958 := by
    simpa [prefixWord, tailWord_2056958, baseEnd_2056958] using wordTrace_append hprefix tailTrace_2056958
  have hstable : (prefixWord ++ tailWord_2056958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056958).length < 2 ^ (prefixWord ++ tailWord_2056958).sum := by decide
  have hdescent : baseEnd_2056958 < baseStart_2056958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2056986 : List Nat := [3, 1, 1, 3, 2, 1, 10]
def baseStart_2056986 : Nat := 118140960795 + 2056986 * 2 ^ 59
def prefixEnd_2056986 : Nat := 4983230072969 + 3 ^ 40 * 2056986 * 2
def baseEnd_2056986 : Nat := 52159136670093544025437

theorem tailTrace_2056986 : CollatzResearch.WordTrace tailWord_2056986 prefixEnd_2056986 52159136670093544025437 := by
  unfold tailWord_2056986
  simp only [CollatzResearch.WordTrace]
  refine ⟨18756110731474625521267703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50016295283932334723380541 18756110731474625521267703)
  ·
    refine ⟨28134166097211938281901555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18756110731474625521267703 28134166097211938281901555)
    ·
      refine ⟨42201249145817907422852333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28134166097211938281901555 42201249145817907422852333)
      ·
        refine ⟨15825468429681715283569625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42201249145817907422852333 15825468429681715283569625)
        ·
          refine ⟨11869101322261286462677219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15825468429681715283569625 11869101322261286462677219)
          ·
            refine ⟨17803651983391929694015829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11869101322261286462677219 17803651983391929694015829)
            ·
              refine ⟨52159136670093544025437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17803651983391929694015829 52159136670093544025437)
              ·
                rfl

theorem cell21_2056986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 10].length) (baseStart_2056986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2056986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2056986 prefixEnd_2056986 := by exact prefixLift 2056986
  have htrace : WordTrace (prefixWord ++ tailWord_2056986) baseStart_2056986 baseEnd_2056986 := by
    simpa [prefixWord, tailWord_2056986, baseEnd_2056986] using wordTrace_append hprefix tailTrace_2056986
  have hstable : (prefixWord ++ tailWord_2056986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2056986).length < 2 ^ (prefixWord ++ tailWord_2056986).sum := by decide
  have hdescent : baseEnd_2056986 < baseStart_2056986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2056986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057034 : List Nat := [3, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_2057034 : Nat := 118140960795 + 2057034 * 2 ^ 59
def prefixEnd_2057034 : Nat := 4983230072969 + 3 ^ 40 * 2057034 * 2
def baseEnd_2057034 : Nat := 469443184284804479428835

theorem tailTrace_2057034 : CollatzResearch.WordTrace tailWord_2057034 prefixEnd_2057034 469443184284804479428835 := by
  unfold tailWord_2057034
  simp only [CollatzResearch.WordTrace]
  refine ⟨18756548407431151570704539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50017462419816404188545437 18756548407431151570704539)
  ·
    refine ⟨28134822611146727356056809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18756548407431151570704539 28134822611146727356056809)
    ·
      refine ⟨21101116958360045517042607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28134822611146727356056809 21101116958360045517042607)
      ·
        refine ⟨31651675437540068275563911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21101116958360045517042607 31651675437540068275563911)
        ·
          refine ⟨47477513156310102413345867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31651675437540068275563911 47477513156310102413345867)
          ·
            refine ⟨71216269734465153620018801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47477513156310102413345867 71216269734465153620018801)
            ·
              refine ⟨53412202300848865215014101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71216269734465153620018801 53412202300848865215014101)
              ·
                refine ⟨1251848491426145278476893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53412202300848865215014101 1251848491426145278476893)
                ·
                  refine ⟨469443184284804479428835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1251848491426145278476893 469443184284804479428835)
                  ·
                    rfl

theorem cell21_2057034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_2057034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057034 prefixEnd_2057034 := by exact prefixLift 2057034
  have htrace : WordTrace (prefixWord ++ tailWord_2057034) baseStart_2057034 baseEnd_2057034 := by
    simpa [prefixWord, tailWord_2057034, baseEnd_2057034] using wordTrace_append hprefix tailTrace_2057034
  have hstable : (prefixWord ++ tailWord_2057034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057034).length < 2 ^ (prefixWord ++ tailWord_2057034).sum := by decide
  have hdescent : baseEnd_2057034 < baseStart_2057034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057037 : List Nat := [1, 6, 1, 2, 3, 1, 7]
def baseStart_2057037 : Nat := 118140960795 + 2057037 * 2 ^ 59
def prefixEnd_2057037 : Nat := 4983230072969 + 3 ^ 40 * 2057037 * 2
def baseEnd_2057037 : Nat := 52160429880630793430981

theorem tailTrace_2057037 : CollatzResearch.WordTrace tailWord_2057037 prefixEnd_2057037 52160429880630793430981 := by
  unfold tailWord_2057037
  simp only [CollatzResearch.WordTrace]
  refine ⟨75026303048713737795177365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50017535365809158530118243 75026303048713737795177365)
  ·
    refine ⟨3516857955408456459148939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75026303048713737795177365 3516857955408456459148939)
    ·
      refine ⟨5275286933112684688723409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3516857955408456459148939 5275286933112684688723409)
      ·
        refine ⟨3956465199834513516542557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5275286933112684688723409 3956465199834513516542557)
        ·
          refine ⟨1483674449937942568703459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3956465199834513516542557 1483674449937942568703459)
          ·
            refine ⟨2225511674906913853055189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1483674449937942568703459 2225511674906913853055189)
            ·
              refine ⟨52160429880630793430981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2225511674906913853055189 52160429880630793430981)
              ·
                rfl

theorem cell21_2057037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 7].length) (baseStart_2057037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057037 prefixEnd_2057037 := by exact prefixLift 2057037
  have htrace : WordTrace (prefixWord ++ tailWord_2057037) baseStart_2057037 baseEnd_2057037 := by
    simpa [prefixWord, tailWord_2057037, baseEnd_2057037] using wordTrace_append hprefix tailTrace_2057037
  have hstable : (prefixWord ++ tailWord_2057037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057037).length < 2 ^ (prefixWord ++ tailWord_2057037).sum := by decide
  have hdescent : baseEnd_2057037 < baseStart_2057037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057124 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_2057124 : Nat := 118140960795 + 2057124 * 2 ^ 59
def prefixEnd_2057124 : Nat := 4983230072969 + 3 ^ 40 * 2057124 * 2
def baseEnd_2057124 : Nat := 469463723510984322928651

theorem tailTrace_2057124 : CollatzResearch.WordTrace tailWord_2057124 prefixEnd_2057124 469463723510984322928651 := by
  unfold tailWord_2057124
  simp only [CollatzResearch.WordTrace]
  refine ⟨37514738099699275826797213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50019650799599034435729617 37514738099699275826797213)
  ·
    refine ⟨14068026787387228435048955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37514738099699275826797213 14068026787387228435048955)
    ·
      refine ⟨21102040181080842652573433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14068026787387228435048955 21102040181080842652573433)
      ·
        refine ⟨15826530135810631989430075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21102040181080842652573433 15826530135810631989430075)
        ·
          refine ⟨23739795203715947984145113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15826530135810631989430075 23739795203715947984145113)
          ·
            refine ⟨17804846402786960988108835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23739795203715947984145113 17804846402786960988108835)
            ·
              refine ⟨26707269604180441482163253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17804846402786960988108835 26707269604180441482163253)
              ·
                refine ⟨2503806525391916388952805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26707269604180441482163253 2503806525391916388952805)
                ·
                  refine ⟨469463723510984322928651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2503806525391916388952805 469463723510984322928651)
                  ·
                    rfl

theorem cell21_2057124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_2057124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057124 prefixEnd_2057124 := by exact prefixLift 2057124
  have htrace : WordTrace (prefixWord ++ tailWord_2057124) baseStart_2057124 baseEnd_2057124 := by
    simpa [prefixWord, tailWord_2057124, baseEnd_2057124] using wordTrace_append hprefix tailTrace_2057124
  have hstable : (prefixWord ++ tailWord_2057124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057124).length < 2 ^ (prefixWord ++ tailWord_2057124).sum := by decide
  have hdescent : baseEnd_2057124 < baseStart_2057124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057169 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 5]
def baseStart_2057169 : Nat := 118140960795 + 2057169 * 2 ^ 59
def prefixEnd_2057169 : Nat := 4983230072969 + 3 ^ 40 * 2057169 * 2
def baseEnd_2057169 : Nat := 469473993124074244678559

theorem tailTrace_2057169 : CollatzResearch.WordTrace tailWord_2057169 prefixEnd_2057169 469473993124074244678559 := by
  unfold tailWord_2057169
  simp only [CollatzResearch.WordTrace]
  refine ⟨75031117484235524338982561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50020744989490349559321707 75031117484235524338982561)
  ·
    refine ⟨56273338113176643254236921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75031117484235524338982561 56273338113176643254236921)
    ·
      refine ⟨42205003584882482440677691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56273338113176643254236921 42205003584882482440677691)
      ·
        refine ⟨63307505377323723661016537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42205003584882482440677691 63307505377323723661016537)
        ·
          refine ⟨47480629032992792745762403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63307505377323723661016537 47480629032992792745762403)
          ·
            refine ⟨71220943549489189118643605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47480629032992792745762403 71220943549489189118643605)
            ·
              refine ⟨3338481728882305739936419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71220943549489189118643605 3338481728882305739936419)
              ·
                refine ⟨5007722593323458609904629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3338481728882305739936419 5007722593323458609904629)
                ·
                  refine ⟨469473993124074244678559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5007722593323458609904629 469473993124074244678559)
                  ·
                    rfl

theorem cell21_2057169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_2057169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057169 prefixEnd_2057169 := by exact prefixLift 2057169
  have htrace : WordTrace (prefixWord ++ tailWord_2057169) baseStart_2057169 baseEnd_2057169 := by
    simpa [prefixWord, tailWord_2057169, baseEnd_2057169] using wordTrace_append hprefix tailTrace_2057169
  have hstable : (prefixWord ++ tailWord_2057169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057169).length < 2 ^ (prefixWord ++ tailWord_2057169).sum := by decide
  have hdescent : baseEnd_2057169 < baseStart_2057169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057189 : List Nat := [1, 3, 1, 6, 1, 2, 2, 5]
def baseStart_2057189 : Nat := 118140960795 + 2057189 * 2 ^ 59
def prefixEnd_2057189 : Nat := 4983230072969 + 3 ^ 40 * 2057189 * 2
def baseEnd_2057189 : Nat := 156492852465519551448395

theorem tailTrace_2057189 : CollatzResearch.WordTrace tailWord_2057189 prefixEnd_2057189 156492852465519551448395 := by
  unfold tailWord_2057189
  simp only [CollatzResearch.WordTrace]
  refine ⟨75031846944163067754710621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50021231296108711836473747 75031846944163067754710621)
  ·
    refine ⟨28136942604061150408016483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75031846944163067754710621 28136942604061150408016483)
    ·
      refine ⟨42205413906091725612024725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28136942604061150408016483 42205413906091725612024725)
      ·
        refine ⟨1978378776848049638063659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42205413906091725612024725 1978378776848049638063659)
        ·
          refine ⟨2967568165272074457095489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978378776848049638063659 2967568165272074457095489)
          ·
            refine ⟨2225676123954055842821617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2967568165272074457095489 2225676123954055842821617)
            ·
              refine ⟨1669257092965541882116213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2225676123954055842821617 1669257092965541882116213)
              ·
                refine ⟨156492852465519551448395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1669257092965541882116213 156492852465519551448395)
                ·
                  rfl

theorem cell21_2057189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 5].length) (baseStart_2057189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057189 prefixEnd_2057189 := by exact prefixLift 2057189
  have htrace : WordTrace (prefixWord ++ tailWord_2057189) baseStart_2057189 baseEnd_2057189 := by
    simpa [prefixWord, tailWord_2057189, baseEnd_2057189] using wordTrace_append hprefix tailTrace_2057189
  have hstable : (prefixWord ++ tailWord_2057189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057189).length < 2 ^ (prefixWord ++ tailWord_2057189).sum := by decide
  have hdescent : baseEnd_2057189 < baseStart_2057189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057276 : List Nat := [2, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_2057276 : Nat := 118140960795 + 2057276 * 2 ^ 59
def prefixEnd_2057276 : Nat := 4983230072969 + 3 ^ 40 * 2057276 * 2
def baseEnd_2057276 : Nat := 469498411981865836395007

theorem tailTrace_2057276 : CollatzResearch.WordTrace tailWord_2057276 prefixEnd_2057276 469498411981865836395007 := by
  unfold tailWord_2057276
  simp only [CollatzResearch.WordTrace]
  refine ⟨37517510047423940806563841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50023346729898587742085121 37517510047423940806563841)
  ·
    refine ⟨28138132535567955604922881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37517510047423940806563841 28138132535567955604922881)
    ·
      refine ⟨21103599401675966703692161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28138132535567955604922881 21103599401675966703692161)
      ·
        refine ⟨15827699551256975027769121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21103599401675966703692161 15827699551256975027769121)
        ·
          refine ⟨11870774663442731270826841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15827699551256975027769121 11870774663442731270826841)
          ·
            refine ⟨8903080997582048453120131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11870774663442731270826841 8903080997582048453120131)
            ·
              refine ⟨13354621496373072679680197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8903080997582048453120131 13354621496373072679680197)
              ·
                refine ⟨2503991530569951127440037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13354621496373072679680197 2503991530569951127440037)
                ·
                  refine ⟨469498411981865836395007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2503991530569951127440037 469498411981865836395007)
                  ·
                    rfl

theorem cell21_2057276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_2057276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057276 prefixEnd_2057276 := by exact prefixLift 2057276
  have htrace : WordTrace (prefixWord ++ tailWord_2057276) baseStart_2057276 baseEnd_2057276 := by
    simpa [prefixWord, tailWord_2057276, baseEnd_2057276] using wordTrace_append hprefix tailTrace_2057276
  have hstable : (prefixWord ++ tailWord_2057276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057276).length < 2 ^ (prefixWord ++ tailWord_2057276).sum := by decide
  have hdescent : baseEnd_2057276 < baseStart_2057276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057290 : List Nat := [3, 1, 2, 1, 1, 2, 5, 6]
def baseStart_2057290 : Nat := 118140960795 + 2057290 * 2 ^ 59
def prefixEnd_2057290 : Nat := 4983230072969 + 3 ^ 40 * 2057290 * 2
def baseEnd_2057290 : Nat := 156500535657534974387215

theorem tailTrace_2057290 : CollatzResearch.WordTrace tailWord_2057290 prefixEnd_2057290 156500535657534974387215 := by
  unfold tailWord_2057290
  simp only [CollatzResearch.WordTrace]
  refine ⟨18758882679199290501034331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50023687144531441336091549 18758882679199290501034331)
  ·
    refine ⟨28138324018798935751551497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18758882679199290501034331 28138324018798935751551497)
    ·
      refine ⟨21103743014099201813663623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28138324018798935751551497 21103743014099201813663623)
      ·
        refine ⟨31655614521148802720495435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21103743014099201813663623 31655614521148802720495435)
        ·
          refine ⟨47483421781723204080743153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31655614521148802720495435 47483421781723204080743153)
          ·
            refine ⟨35612566336292403060557365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47483421781723204080743153 35612566336292403060557365)
            ·
              refine ⟨3338678094027412786927253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35612566336292403060557365 3338678094027412786927253)
              ·
                refine ⟨156500535657534974387215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3338678094027412786927253 156500535657534974387215)
                ·
                  rfl

theorem cell21_2057290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_2057290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057290 prefixEnd_2057290 := by exact prefixLift 2057290
  have htrace : WordTrace (prefixWord ++ tailWord_2057290) baseStart_2057290 baseEnd_2057290 := by
    simpa [prefixWord, tailWord_2057290, baseEnd_2057290] using wordTrace_append hprefix tailTrace_2057290
  have hstable : (prefixWord ++ tailWord_2057290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057290).length < 2 ^ (prefixWord ++ tailWord_2057290).sum := by decide
  have hdescent : baseEnd_2057290 < baseStart_2057290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057293 : List Nat := [1, 6, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2057293 : Nat := 118140960795 + 2057293 * 2 ^ 59
def prefixEnd_2057293 : Nat := 4983230072969 + 3 ^ 40 * 2057293 * 2
def baseEnd_2057293 : Nat := 469502291613477584611639

theorem tailTrace_2057293 : CollatzResearch.WordTrace tailWord_2057293 prefixEnd_2057293 469502291613477584611639 := by
  unfold tailWord_2057293
  simp only [CollatzResearch.WordTrace]
  refine ⟨75035640135786293516496533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50023760090524195677664355 75035640135786293516496533)
  ·
    refine ⟨3517295631364982508585775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75035640135786293516496533 3517295631364982508585775)
    ·
      refine ⟨5275943447047473762878663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3517295631364982508585775 5275943447047473762878663)
      ·
        refine ⟨7913915170571210644317995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5275943447047473762878663 7913915170571210644317995)
        ·
          refine ⟨11870872755856815966476993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7913915170571210644317995 11870872755856815966476993)
          ·
            refine ⟨8903154566892611974857745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11870872755856815966476993 8903154566892611974857745)
            ·
              refine ⟨6677365925169458981143309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8903154566892611974857745 6677365925169458981143309)
              ·
                refine ⟨2504012221938547117928741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6677365925169458981143309 2504012221938547117928741)
                ·
                  refine ⟨469502291613477584611639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504012221938547117928741 469502291613477584611639)
                  ·
                    rfl

theorem cell21_2057293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2057293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057293 prefixEnd_2057293 := by exact prefixLift 2057293
  have htrace : WordTrace (prefixWord ++ tailWord_2057293) baseStart_2057293 baseEnd_2057293 := by
    simpa [prefixWord, tailWord_2057293, baseEnd_2057293] using wordTrace_append hprefix tailTrace_2057293
  have hstable : (prefixWord ++ tailWord_2057293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057293).length < 2 ^ (prefixWord ++ tailWord_2057293).sum := by decide
  have hdescent : baseEnd_2057293 < baseStart_2057293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057335 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 6]
def baseStart_2057335 : Nat := 118140960795 + 2057335 * 2 ^ 59
def prefixEnd_2057335 : Nat := 4983230072969 + 3 ^ 40 * 2057335 * 2
def baseEnd_2057335 : Nat := 469511876585694844911553

theorem tailTrace_2057335 : CollatzResearch.WordTrace tailWord_2057335 prefixEnd_2057335 469511876585694844911553 := by
  unfold tailWord_2057335
  simp only [CollatzResearch.WordTrace]
  refine ⟨75037172001634134689525459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50024781334422756459683639 75037172001634134689525459)
  ·
    refine ⟨112555758002451202034288189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75037172001634134689525459 112555758002451202034288189)
    ·
      refine ⟨42208409250919200762858071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112555758002451202034288189 42208409250919200762858071)
      ·
        refine ⟨63312613876378801144287107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42208409250919200762858071 63312613876378801144287107)
        ·
          refine ⟨94968920814568201716430661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63312613876378801144287107 94968920814568201716430661)
          ·
            refine ⟨17806672652731537821830749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94968920814568201716430661 17806672652731537821830749)
            ·
              refine ⟨6677502244774326683186531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17806672652731537821830749 6677502244774326683186531)
              ·
                refine ⟨10016253367161490024779797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6677502244774326683186531 10016253367161490024779797)
                ·
                  refine ⟨469511876585694844911553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10016253367161490024779797 469511876585694844911553)
                  ·
                    rfl

theorem cell21_2057335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_2057335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057335 prefixEnd_2057335 := by exact prefixLift 2057335
  have htrace : WordTrace (prefixWord ++ tailWord_2057335) baseStart_2057335 baseEnd_2057335 := by
    simpa [prefixWord, tailWord_2057335, baseEnd_2057335] using wordTrace_append hprefix tailTrace_2057335
  have hstable : (prefixWord ++ tailWord_2057335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057335).length < 2 ^ (prefixWord ++ tailWord_2057335).sum := by decide
  have hdescent : baseEnd_2057335 < baseStart_2057335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057383 : List Nat := [1, 1, 6, 2, 1, 3, 7]
def baseStart_2057383 : Nat := 118140960795 + 2057383 * 2 ^ 59
def prefixEnd_2057383 : Nat := 4983230072969 + 3 ^ 40 * 2057383 * 2
def baseEnd_2057383 : Nat := 52169203426628603123495

theorem tailTrace_2057383 : CollatzResearch.WordTrace tailWord_2057383 prefixEnd_2057383 52169203426628603123495 := by
  unfold tailWord_2057383
  simp only [CollatzResearch.WordTrace]
  refine ⟨75038922705460238887272803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50025948470306825924848535 75038922705460238887272803)
  ·
    refine ⟨112558384058190358330909205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75038922705460238887272803 112558384058190358330909205)
    ·
      refine ⟨5276174252727673046761369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112558384058190358330909205 5276174252727673046761369)
      ·
        refine ⟨3957130689545754785071027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5276174252727673046761369 3957130689545754785071027)
        ·
          refine ⟨5935696034318632177606541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957130689545754785071027 5935696034318632177606541)
          ·
            refine ⟨2225886012869487066602453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5935696034318632177606541 2225886012869487066602453)
            ·
              refine ⟨52169203426628603123495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2225886012869487066602453 52169203426628603123495)
              ·
                rfl

theorem cell21_2057383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 7].length) (baseStart_2057383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057383 prefixEnd_2057383 := by exact prefixLift 2057383
  have htrace : WordTrace (prefixWord ++ tailWord_2057383) baseStart_2057383 baseEnd_2057383 := by
    simpa [prefixWord, tailWord_2057383, baseEnd_2057383] using wordTrace_append hprefix tailTrace_2057383
  have hstable : (prefixWord ++ tailWord_2057383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057383).length < 2 ^ (prefixWord ++ tailWord_2057383).sum := by decide
  have hdescent : baseEnd_2057383 < baseStart_2057383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057445 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 4]
def baseStart_2057445 : Nat := 118140960795 + 2057445 * 2 ^ 59
def prefixEnd_2057445 : Nat := 4983230072969 + 3 ^ 40 * 2057445 * 2
def baseEnd_2057445 : Nat := 469536980084359098077995

theorem tailTrace_2057445 : CollatzResearch.WordTrace tailWord_2057445 prefixEnd_2057445 469536980084359098077995 := by
  unfold tailWord_2057445
  simp only [CollatzResearch.WordTrace]
  refine ⟨75041184031235623476029789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50027456020823748984019859 75041184031235623476029789)
  ·
    refine ⟨28140444011713358803511171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75041184031235623476029789 28140444011713358803511171)
    ·
      refine ⟨42210666017570038205266757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28140444011713358803511171 42210666017570038205266757)
      ·
        refine ⟨7914499878294382163487517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42210666017570038205266757 7914499878294382163487517)
        ·
          refine ⟨2967937454360393311307819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7914499878294382163487517 2967937454360393311307819)
          ·
            refine ⟨4451906181540589966961729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2967937454360393311307819 4451906181540589966961729)
            ·
              refine ⟨3338929636155442475221297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4451906181540589966961729 3338929636155442475221297)
              ·
                refine ⟨2504197227116581856415973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3338929636155442475221297 2504197227116581856415973)
                ·
                  refine ⟨469536980084359098077995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504197227116581856415973 469536980084359098077995)
                  ·
                    rfl

theorem cell21_2057445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_2057445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057445 prefixEnd_2057445 := by exact prefixLift 2057445
  have htrace : WordTrace (prefixWord ++ tailWord_2057445) baseStart_2057445 baseEnd_2057445 := by
    simpa [prefixWord, tailWord_2057445, baseEnd_2057445] using wordTrace_append hprefix tailTrace_2057445
  have hstable : (prefixWord ++ tailWord_2057445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057445).length < 2 ^ (prefixWord ++ tailWord_2057445).sum := by decide
  have hdescent : baseEnd_2057445 < baseStart_2057445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057473 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 5]
def baseStart_2057473 : Nat := 118140960795 + 2057473 * 2 ^ 59
def prefixEnd_2057473 : Nat := 4983230072969 + 3 ^ 40 * 2057473 * 2
def baseEnd_2057473 : Nat := 469543370065837271611271

theorem tailTrace_2057473 : CollatzResearch.WordTrace tailWord_2057473 prefixEnd_2057473 469543370065837271611271 := by
  unfold tailWord_2057473
  simp only [CollatzResearch.WordTrace]
  refine ⟨75042205275134184258049073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50028136850089456172032715 75042205275134184258049073)
  ·
    refine ⟨56281653956350638193536805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75042205275134184258049073 56281653956350638193536805)
    ·
      refine ⟨10552810116815744661288151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56281653956350638193536805 10552810116815744661288151)
      ·
        refine ⟨15829215175223616991932227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10552810116815744661288151 15829215175223616991932227)
        ·
          refine ⟨23743822762835425487898341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15829215175223616991932227 23743822762835425487898341)
          ·
            refine ⟨4451966768031642278980939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23743822762835425487898341 4451966768031642278980939)
            ·
              refine ⟨6677950152047463418471409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4451966768031642278980939 6677950152047463418471409)
              ·
                refine ⟨5008462614035597563853557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6677950152047463418471409 5008462614035597563853557)
                ·
                  refine ⟨469543370065837271611271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5008462614035597563853557 469543370065837271611271)
                  ·
                    rfl

theorem cell21_2057473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_2057473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057473 prefixEnd_2057473 := by exact prefixLift 2057473
  have htrace : WordTrace (prefixWord ++ tailWord_2057473) baseStart_2057473 baseEnd_2057473 := by
    simpa [prefixWord, tailWord_2057473, baseEnd_2057473] using wordTrace_append hprefix tailTrace_2057473
  have hstable : (prefixWord ++ tailWord_2057473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057473).length < 2 ^ (prefixWord ++ tailWord_2057473).sum := by decide
  have hdescent : baseEnd_2057473 < baseStart_2057473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057504 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_2057504 : Nat := 118140960795 + 2057504 * 2 ^ 59
def prefixEnd_2057504 : Nat := 4983230072969 + 3 ^ 40 * 2057504 * 2
def baseEnd_2057504 : Nat := 469550444688188106594541

theorem tailTrace_2057504 : CollatzResearch.WordTrace tailWord_2057504 prefixEnd_2057504 469550444688188106594541 := by
  unfold tailWord_2057504
  simp only [CollatzResearch.WordTrace]
  refine ⟨37521667969010938276213783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50028890625347917701618377 37521667969010938276213783)
  ·
    refine ⟨56282501953516407414320675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37521667969010938276213783 56282501953516407414320675)
    ·
      refine ⟨84423752930274611121481013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56282501953516407414320675 84423752930274611121481013)
      ·
        refine ⟨7914726837213244792638845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84423752930274611121481013 7914726837213244792638845)
        ·
          refine ⟨2968022563954966797239567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7914726837213244792638845 2968022563954966797239567)
          ·
            refine ⟨4452033845932450195859351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968022563954966797239567 4452033845932450195859351)
            ·
              refine ⟨6678050768898675293789027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452033845932450195859351 6678050768898675293789027)
              ·
                refine ⟨10017076153348012940683541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6678050768898675293789027 10017076153348012940683541)
                ·
                  refine ⟨469550444688188106594541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10017076153348012940683541 469550444688188106594541)
                  ·
                    rfl

theorem cell21_2057504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_2057504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057504 prefixEnd_2057504 := by exact prefixLift 2057504
  have htrace : WordTrace (prefixWord ++ tailWord_2057504) baseStart_2057504 baseEnd_2057504 := by
    simpa [prefixWord, tailWord_2057504, baseEnd_2057504] using wordTrace_append hprefix tailTrace_2057504
  have hstable : (prefixWord ++ tailWord_2057504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057504).length < 2 ^ (prefixWord ++ tailWord_2057504).sum := by decide
  have hdescent : baseEnd_2057504 < baseStart_2057504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057521 : List Nat := [1, 2, 2, 3, 3, 2, 3, 1, 4]
def baseStart_2057521 : Nat := 118140960795 + 2057521 * 2 ^ 59
def prefixEnd_2057521 : Nat := 4983230072969 + 3 ^ 40 * 2057521 * 2
def baseEnd_2057521 : Nat := 469554324319799854811173

theorem tailTrace_2057521 : CollatzResearch.WordTrace tailWord_2057521 prefixEnd_2057521 469554324319799854811173 := by
  unfold tailWord_2057521
  simp only [CollatzResearch.WordTrace]
  refine ⟨75043955978960288455796417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50029303985973525637197611 75043955978960288455796417)
  ·
    refine ⟨56282966984220216341847313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75043955978960288455796417 56282966984220216341847313)
    ·
      refine ⟨42212225238165162256385485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56282966984220216341847313 42212225238165162256385485)
      ·
        refine ⟨15829584464311935846144557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42212225238165162256385485 15829584464311935846144557)
        ·
          refine ⟨5936094174116975942304209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15829584464311935846144557 5936094174116975942304209)
          ·
            refine ⟨4452070630587731956728157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5936094174116975942304209 4452070630587731956728157)
            ·
              refine ⟨1669526486470399483773059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4452070630587731956728157 1669526486470399483773059)
              ·
                refine ⟨2504289729705599225659589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669526486470399483773059 2504289729705599225659589)
                ·
                  refine ⟨469554324319799854811173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504289729705599225659589 469554324319799854811173)
                  ·
                    rfl

theorem cell21_2057521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_2057521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057521 prefixEnd_2057521 := by exact prefixLift 2057521
  have htrace : WordTrace (prefixWord ++ tailWord_2057521) baseStart_2057521 baseEnd_2057521 := by
    simpa [prefixWord, tailWord_2057521, baseEnd_2057521] using wordTrace_append hprefix tailTrace_2057521
  have hstable : (prefixWord ++ tailWord_2057521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057521).length < 2 ^ (prefixWord ++ tailWord_2057521).sum := by decide
  have hdescent : baseEnd_2057521 < baseStart_2057521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057535 : List Nat := [1, 1, 2, 2, 4, 4, 2, 5]
def baseStart_2057535 : Nat := 118140960795 + 2057535 * 2 ^ 59
def prefixEnd_2057535 : Nat := 4983230072969 + 3 ^ 40 * 2057535 * 2
def baseEnd_2057535 : Nat := 156519173103512980525937

theorem tailTrace_2057535 : CollatzResearch.WordTrace tailWord_2057535 prefixEnd_2057535 156519173103512980525937 := by
  unfold tailWord_2057535
  simp only [CollatzResearch.WordTrace]
  refine ⟨75044466600909568846806059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50029644400606379231204039 75044466600909568846806059)
  ·
    refine ⟨112566699901364353270209089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75044466600909568846806059 112566699901364353270209089)
    ·
      refine ⟨84425024926023264952656817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112566699901364353270209089 84425024926023264952656817)
      ·
        refine ⟨63318768694517448714492613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84425024926023264952656817 63318768694517448714492613)
        ·
          refine ⟨11872269130222021633967365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63318768694517448714492613 11872269130222021633967365)
          ·
            refine ⟨2226050461916629056368881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11872269130222021633967365 2226050461916629056368881)
            ·
              refine ⟨1669537846437471792276661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226050461916629056368881 1669537846437471792276661)
              ·
                refine ⟨156519173103512980525937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1669537846437471792276661 156519173103512980525937)
                ·
                  rfl

theorem cell21_2057535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 5].length) (baseStart_2057535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057535 prefixEnd_2057535 := by exact prefixLift 2057535
  have htrace : WordTrace (prefixWord ++ tailWord_2057535) baseStart_2057535 baseEnd_2057535 := by
    simpa [prefixWord, tailWord_2057535, baseEnd_2057535] using wordTrace_append hprefix tailTrace_2057535
  have hstable : (prefixWord ++ tailWord_2057535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057535).length < 2 ^ (prefixWord ++ tailWord_2057535).sum := by decide
  have hdescent : baseEnd_2057535 < baseStart_2057535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057558 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2057558 : Nat := 118140960795 + 2057558 * 2 ^ 59
def prefixEnd_2057558 : Nat := 4983230072969 + 3 ^ 40 * 2057558 * 2
def baseEnd_2057558 : Nat := 469562768223896012694431

theorem tailTrace_2057558 : CollatzResearch.WordTrace tailWord_2057558 prefixEnd_2057558 469562768223896012694431 := by
  unfold tailWord_2057558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4690331592489140235930833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50030203653217495849928885 4690331592489140235930833)
  ·
    refine ⟨3517748694366855176948125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4690331592489140235930833 3517748694366855176948125)
    ·
      refine ⟨1319155760387570691355547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3517748694366855176948125 1319155760387570691355547)
      ·
        refine ⟨1978733640581356037033321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319155760387570691355547 1978733640581356037033321)
        ·
          refine ⟨1484050230436017027774991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1978733640581356037033321 1484050230436017027774991)
          ·
            refine ⟨2226075345654025541662487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484050230436017027774991 2226075345654025541662487)
            ·
              refine ⟨3339113018481038312493731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226075345654025541662487 3339113018481038312493731)
              ·
                refine ⟨5008669527721557468740597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339113018481038312493731 5008669527721557468740597)
                ·
                  refine ⟨469562768223896012694431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5008669527721557468740597 469562768223896012694431)
                  ·
                    rfl

theorem cell21_2057558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2057558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057558 prefixEnd_2057558 := by exact prefixLift 2057558
  have htrace : WordTrace (prefixWord ++ tailWord_2057558) baseStart_2057558 baseEnd_2057558 := by
    simpa [prefixWord, tailWord_2057558, baseEnd_2057558] using wordTrace_append hprefix tailTrace_2057558
  have hstable : (prefixWord ++ tailWord_2057558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057558).length < 2 ^ (prefixWord ++ tailWord_2057558).sum := by decide
  have hdescent : baseEnd_2057558 < baseStart_2057558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057580 : List Nat := [2, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_2057580 : Nat := 118140960795 + 2057580 * 2 ^ 59
def prefixEnd_2057580 : Nat := 4983230072969 + 3 ^ 40 * 2057580 * 2
def baseEnd_2057580 : Nat := 469567788923628863327719

theorem tailTrace_2057580 : CollatzResearch.WordTrace tailWord_2057580 prefixEnd_2057580 469567788923628863327719 := by
  unfold tailWord_2057580
  simp only [CollatzResearch.WordTrace]
  refine ⟨37523053942873270766097097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50030738590497694354796129 37523053942873270766097097)
  ·
    refine ⟨28142290457154953074572823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37523053942873270766097097 28142290457154953074572823)
    ·
      refine ⟨42213435685732429611859235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28142290457154953074572823 42213435685732429611859235)
      ·
        refine ⟨63320153528598644417788853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42213435685732429611859235 63320153528598644417788853)
        ·
          refine ⟨5936264393306122914167705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63320153528598644417788853 5936264393306122914167705)
          ·
            refine ⟨4452198294979592185625779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5936264393306122914167705 4452198294979592185625779)
            ·
              refine ⟨6678297442469388278438669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4452198294979592185625779 6678297442469388278438669)
              ·
                refine ⟨2504361540926020604414501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6678297442469388278438669 2504361540926020604414501)
                ·
                  refine ⟨469567788923628863327719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504361540926020604414501 469567788923628863327719)
                  ·
                    rfl

theorem cell21_2057580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_2057580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057580 prefixEnd_2057580 := by exact prefixLift 2057580
  have htrace : WordTrace (prefixWord ++ tailWord_2057580) baseStart_2057580 baseEnd_2057580 := by
    simpa [prefixWord, tailWord_2057580, baseEnd_2057580] using wordTrace_append hprefix tailTrace_2057580
  have hstable : (prefixWord ++ tailWord_2057580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057580).length < 2 ^ (prefixWord ++ tailWord_2057580).sum := by decide
  have hdescent : baseEnd_2057580 < baseStart_2057580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057628 : List Nat := [2, 2, 3, 4, 1, 2, 1, 6]
def baseStart_2057628 : Nat := 118140960795 + 2057628 * 2 ^ 59
def prefixEnd_2057628 : Nat := 4983230072969 + 3 ^ 40 * 2057628 * 2
def baseEnd_2057628 : Nat := 156526247725863815509207

theorem tailTrace_2057628 : CollatzResearch.WordTrace tailWord_2057628 prefixEnd_2057628 156526247725863815509207 := by
  unfold tailWord_2057628
  simp only [CollatzResearch.WordTrace]
  refine ⟨37523929294786322864970769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50031905726381763819961025 37523929294786322864970769)
  ·
    refine ⟨28142946971089742148728077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37523929294786322864970769 28142946971089742148728077)
    ·
      refine ⟨10553605114158653305773029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28142946971089742148728077 10553605114158653305773029)
      ·
        refine ⟨1978800958904747494832443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10553605114158653305773029 1978800958904747494832443)
        ·
          refine ⟨2968201438357121242248665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978800958904747494832443 2968201438357121242248665)
          ·
            refine ⟨2226151078767840931686499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2968201438357121242248665 2226151078767840931686499)
            ·
              refine ⟨3339226618151761397529749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226151078767840931686499 3339226618151761397529749)
              ·
                refine ⟨156526247725863815509207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3339226618151761397529749 156526247725863815509207)
                ·
                  rfl

theorem cell21_2057628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_2057628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057628 prefixEnd_2057628 := by exact prefixLift 2057628
  have htrace : WordTrace (prefixWord ++ tailWord_2057628) baseStart_2057628 baseEnd_2057628 := by
    simpa [prefixWord, tailWord_2057628, baseEnd_2057628] using wordTrace_append hprefix tailTrace_2057628
  have hstable : (prefixWord ++ tailWord_2057628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057628).length < 2 ^ (prefixWord ++ tailWord_2057628).sum := by decide
  have hdescent : baseEnd_2057628 < baseStart_2057628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057701 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 5]
def baseStart_2057701 : Nat := 118140960795 + 2057701 * 2 ^ 59
def prefixEnd_2057701 : Nat := 4983230072969 + 3 ^ 40 * 2057701 * 2
def baseEnd_2057701 : Nat := 469595402772159541810805

theorem tailTrace_2057701 : CollatzResearch.WordTrace tailWord_2057701 prefixEnd_2057701 469595402772159541810805 := by
  unfold tailWord_2057701
  simp only [CollatzResearch.WordTrace]
  refine ⟨75050521118308179197348957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50033680745538786131565971 75050521118308179197348957)
  ·
    refine ⟨28143945419365567199005859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75050521118308179197348957 28143945419365567199005859)
    ·
      refine ⟨42215918129048350798508789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28143945419365567199005859 42215918129048350798508789)
      ·
        refine ⟨3957742324598282887360199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42215918129048350798508789 3957742324598282887360199)
        ·
          refine ⟨5936613486897424331040299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957742324598282887360199 5936613486897424331040299)
          ·
            refine ⟨8904920230346136496560449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5936613486897424331040299 8904920230346136496560449)
            ·
              refine ⟨6678690172759602372420337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8904920230346136496560449 6678690172759602372420337)
              ·
                refine ⟨5009017629569701779315253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6678690172759602372420337 5009017629569701779315253)
                ·
                  refine ⟨469595402772159541810805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5009017629569701779315253 469595402772159541810805)
                  ·
                    rfl

theorem cell21_2057701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_2057701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057701 prefixEnd_2057701 := by exact prefixLift 2057701
  have htrace : WordTrace (prefixWord ++ tailWord_2057701) baseStart_2057701 baseEnd_2057701 := by
    simpa [prefixWord, tailWord_2057701, baseEnd_2057701] using wordTrace_append hprefix tailTrace_2057701
  have hstable : (prefixWord ++ tailWord_2057701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057701).length < 2 ^ (prefixWord ++ tailWord_2057701).sum := by decide
  have hdescent : baseEnd_2057701 < baseStart_2057701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057735 : List Nat := [1, 1, 4, 3, 2, 2, 3, 2, 3]
def baseStart_2057735 : Nat := 118140960795 + 2057735 * 2 ^ 59
def prefixEnd_2057735 : Nat := 4983230072969 + 3 ^ 40 * 2057735 * 2
def baseEnd_2057735 : Nat := 469603162035383038244069

theorem tailTrace_2057735 : CollatzResearch.WordTrace tailWord_2057735 prefixEnd_2057735 469603162035383038244069 := by
  unfold tailWord_2057735
  simp only [CollatzResearch.WordTrace]
  refine ⟨75051761200185003004086659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50034507466790002002724439 75051761200185003004086659)
  ·
    refine ⟨112577641800277504506129989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75051761200185003004086659 112577641800277504506129989)
    ·
      refine ⟨21108307837552032094899373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112577641800277504506129989 21108307837552032094899373)
      ·
        refine ⟨7915615439082012035587265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21108307837552032094899373 7915615439082012035587265)
        ·
          refine ⟨5936711579311509026690449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7915615439082012035587265 5936711579311509026690449)
          ·
            refine ⟨4452533684483631770017837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5936711579311509026690449 4452533684483631770017837)
            ·
              refine ⟨1669700131681361913756689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4452533684483631770017837 1669700131681361913756689)
              ·
                refine ⟨1252275098761021435317517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1669700131681361913756689 1252275098761021435317517)
                ·
                  refine ⟨469603162035383038244069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252275098761021435317517 469603162035383038244069)
                  ·
                    rfl

theorem cell21_2057735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 2, 3].length) (baseStart_2057735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057735 prefixEnd_2057735 := by exact prefixLift 2057735
  have htrace : WordTrace (prefixWord ++ tailWord_2057735) baseStart_2057735 baseEnd_2057735 := by
    simpa [prefixWord, tailWord_2057735, baseEnd_2057735] using wordTrace_append hprefix tailTrace_2057735
  have hstable : (prefixWord ++ tailWord_2057735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057735).length < 2 ^ (prefixWord ++ tailWord_2057735).sum := by decide
  have hdescent : baseEnd_2057735 < baseStart_2057735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057749 : List Nat := [1, 3, 2, 1, 3, 4, 2, 1, 4]
def baseStart_2057749 : Nat := 118140960795 + 2057749 * 2 ^ 59
def prefixEnd_2057749 : Nat := 4983230072969 + 3 ^ 40 * 2057749 * 2
def baseEnd_2057749 : Nat := 469606357026122125010707

theorem tailTrace_2057749 : CollatzResearch.WordTrace tailWord_2057749 prefixEnd_2057749 469606357026122125010707 := by
  unfold tailWord_2057749
  simp only [CollatzResearch.WordTrace]
  refine ⟨75052271822134283395096301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50034847881422855596730867 75052271822134283395096301)
  ·
    refine ⟨28144601933300356273161113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75052271822134283395096301 28144601933300356273161113)
    ·
      refine ⟨21108451449975267204870835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28144601933300356273161113 21108451449975267204870835)
      ·
        refine ⟨31662677174962900807306253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21108451449975267204870835 31662677174962900807306253)
        ·
          refine ⟨11873503940611087802739845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31662677174962900807306253 11873503940611087802739845)
          ·
            refine ⟨2226281988864578963013721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11873503940611087802739845 2226281988864578963013721)
            ·
              refine ⟨1669711491648434222260291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226281988864578963013721 1669711491648434222260291)
              ·
                refine ⟨2504567237472651333390437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669711491648434222260291 2504567237472651333390437)
                ·
                  refine ⟨469606357026122125010707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504567237472651333390437 469606357026122125010707)
                  ·
                    rfl

theorem cell21_2057749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_2057749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057749 prefixEnd_2057749 := by exact prefixLift 2057749
  have htrace : WordTrace (prefixWord ++ tailWord_2057749) baseStart_2057749 baseEnd_2057749 := by
    simpa [prefixWord, tailWord_2057749, baseEnd_2057749] using wordTrace_append hprefix tailTrace_2057749
  have hstable : (prefixWord ++ tailWord_2057749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057749).length < 2 ^ (prefixWord ++ tailWord_2057749).sum := by decide
  have hdescent : baseEnd_2057749 < baseStart_2057749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057777 : List Nat := [1, 2, 2, 3, 1, 1, 1, 7, 3]
def baseStart_2057777 : Nat := 118140960795 + 2057777 * 2 ^ 59
def prefixEnd_2057777 : Nat := 4983230072969 + 3 ^ 40 * 2057777 * 2
def baseEnd_2057777 : Nat := 469612747007600298543983

theorem tailTrace_2057777 : CollatzResearch.WordTrace tailWord_2057777 prefixEnd_2057777 469612747007600298543983 := by
  unfold tailWord_2057777
  simp only [CollatzResearch.WordTrace]
  refine ⟨75053293066032844177115585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50035528710688562784743723 75053293066032844177115585)
  ·
    refine ⟨56289969799524633132836689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75053293066032844177115585 56289969799524633132836689)
    ·
      refine ⟨42217477349643474849627517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56289969799524633132836689 42217477349643474849627517)
      ·
        refine ⟨15831554006116303068610319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42217477349643474849627517 15831554006116303068610319)
        ·
          refine ⟨23747331009174454602915479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15831554006116303068610319 23747331009174454602915479)
          ·
            refine ⟨35620996513761681904373219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23747331009174454602915479 35620996513761681904373219)
            ·
              refine ⟨53431494770642522856559829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35620996513761681904373219 53431494770642522856559829)
              ·
                refine ⟨1252300658686934129450621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53431494770642522856559829 1252300658686934129450621)
                ·
                  refine ⟨469612747007600298543983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252300658686934129450621 469612747007600298543983)
                  ·
                    rfl

theorem cell21_2057777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_2057777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057777 prefixEnd_2057777 := by exact prefixLift 2057777
  have htrace : WordTrace (prefixWord ++ tailWord_2057777) baseStart_2057777 baseEnd_2057777 := by
    simpa [prefixWord, tailWord_2057777, baseEnd_2057777] using wordTrace_append hprefix tailTrace_2057777
  have hstable : (prefixWord ++ tailWord_2057777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057777).length < 2 ^ (prefixWord ++ tailWord_2057777).sum := by decide
  have hdescent : baseEnd_2057777 < baseStart_2057777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057791 : List Nat := [1, 1, 2, 2, 3, 3, 1, 4, 4]
def baseStart_2057791 : Nat := 118140960795 + 2057791 * 2 ^ 59
def prefixEnd_2057791 : Nat := 4983230072969 + 3 ^ 40 * 2057791 * 2
def baseEnd_2057791 : Nat := 469615941998339385310621

theorem tailTrace_2057791 : CollatzResearch.WordTrace tailWord_2057791 prefixEnd_2057791 469615941998339385310621 := by
  unfold tailWord_2057791
  simp only [CollatzResearch.WordTrace]
  refine ⟨75053803687982124568125227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50035869125321416378750151 75053803687982124568125227)
  ·
    refine ⟨112580705531973186852187841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75053803687982124568125227 112580705531973186852187841)
    ·
      refine ⟨84435529148979890139140881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112580705531973186852187841 84435529148979890139140881)
      ·
        refine ⟨63326646861734917604355661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84435529148979890139140881 63326646861734917604355661)
        ·
          refine ⟨23747492573150594101633373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63326646861734917604355661 23747492573150594101633373)
          ·
            refine ⟨8905309714931472788112515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23747492573150594101633373 8905309714931472788112515)
            ·
              refine ⟨13357964572397209182168773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8905309714931472788112515 13357964572397209182168773)
              ·
                refine ⟨2504618357324476721656645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13357964572397209182168773 2504618357324476721656645)
                ·
                  refine ⟨469615941998339385310621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504618357324476721656645 469615941998339385310621)
                  ·
                    rfl

theorem cell21_2057791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 4].length) (baseStart_2057791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057791 prefixEnd_2057791 := by exact prefixLift 2057791
  have htrace : WordTrace (prefixWord ++ tailWord_2057791) baseStart_2057791 baseEnd_2057791 := by
    simpa [prefixWord, tailWord_2057791, baseEnd_2057791] using wordTrace_append hprefix tailTrace_2057791
  have hstable : (prefixWord ++ tailWord_2057791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057791).length < 2 ^ (prefixWord ++ tailWord_2057791).sum := by decide
  have hdescent : baseEnd_2057791 < baseStart_2057791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057853 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2057853 : Nat := 118140960795 + 2057853 * 2 ^ 59
def prefixEnd_2057853 : Nat := 4983230072969 + 3 ^ 40 * 2057853 * 2
def baseEnd_2057853 : Nat := 469630091243041055277161

theorem tailTrace_2057853 : CollatzResearch.WordTrace tailWord_2057853 prefixEnd_2057853 469630091243041055277161 := by
  unfold tailWord_2057853
  simp only [CollatzResearch.WordTrace]
  refine ⟨75056065013757509156882213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50037376675838339437921475 75056065013757509156882213)
  ·
    refine ⟨14073012190079532966915415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75056065013757509156882213 14073012190079532966915415)
    ·
      refine ⟨21109518285119299450373123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14073012190079532966915415 21109518285119299450373123)
      ·
        refine ⟨31664277427678949175559685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21109518285119299450373123 31664277427678949175559685)
        ·
          refine ⟨5937052017689802970417441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31664277427678949175559685 5937052017689802970417441)
          ·
            refine ⟨4452789013267352227813081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5937052017689802970417441 4452789013267352227813081)
            ·
              refine ⟨3339591759950514170859811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4452789013267352227813081 3339591759950514170859811)
              ·
                refine ⟨5009387639925771256289717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3339591759950514170859811 5009387639925771256289717)
                ·
                  refine ⟨469630091243041055277161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5009387639925771256289717 469630091243041055277161)
                  ·
                    rfl

theorem cell21_2057853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2057853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057853 prefixEnd_2057853 := by exact prefixLift 2057853
  have htrace : WordTrace (prefixWord ++ tailWord_2057853) baseStart_2057853 baseEnd_2057853 := by
    simpa [prefixWord, tailWord_2057853, baseEnd_2057853] using wordTrace_append hprefix tailTrace_2057853
  have hstable : (prefixWord ++ tailWord_2057853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057853).length < 2 ^ (prefixWord ++ tailWord_2057853).sum := by decide
  have hdescent : baseEnd_2057853 < baseStart_2057853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057960 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_2057960 : Nat := 118140960795 + 2057960 * 2 ^ 59
def prefixEnd_2057960 : Nat := 4983230072969 + 3 ^ 40 * 2057960 * 2
def baseEnd_2057960 : Nat := 469654510100832646993609

theorem tailTrace_2057960 : CollatzResearch.WordTrace tailWord_2057960 prefixEnd_2057960 469654510100832646993609 := by
  unfold tailWord_2057960
  simp only [CollatzResearch.WordTrace]
  refine ⟨37529983812184933215513667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50039978416246577620684889 37529983812184933215513667)
  ·
    refine ⟨56294975718277399823270501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37529983812184933215513667 56294975718277399823270501)
    ·
      refine ⟨10555307947177012466863219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56294975718277399823270501 10555307947177012466863219)
      ·
        refine ⟨15832961920765518700294829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10555307947177012466863219 15832961920765518700294829)
        ·
          refine ⟨5937360720287069512610561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15832961920765518700294829 5937360720287069512610561)
          ·
            refine ⟨4453020540215302134457921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5937360720287069512610561 4453020540215302134457921)
            ·
              refine ⟨3339765405161476600843441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4453020540215302134457921 3339765405161476600843441)
              ·
                refine ⟨2504824053871107450632581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3339765405161476600843441 2504824053871107450632581)
                ·
                  refine ⟨469654510100832646993609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504824053871107450632581 469654510100832646993609)
                  ·
                    rfl

theorem cell21_2057960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_2057960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057960 prefixEnd_2057960 := by exact prefixLift 2057960
  have htrace : WordTrace (prefixWord ++ tailWord_2057960) baseStart_2057960 baseEnd_2057960 := by
    simpa [prefixWord, tailWord_2057960, baseEnd_2057960] using wordTrace_append hprefix tailTrace_2057960
  have hstable : (prefixWord ++ tailWord_2057960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057960).length < 2 ^ (prefixWord ++ tailWord_2057960).sum := by decide
  have hdescent : baseEnd_2057960 < baseStart_2057960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057974 : List Nat := [5, 1, 1, 1, 1, 3, 3, 6]
def baseStart_2057974 : Nat := 118140960795 + 2057974 * 2 ^ 59
def prefixEnd_2057974 : Nat := 4983230072969 + 3 ^ 40 * 2057974 * 2
def baseEnd_2057974 : Nat := 156552568363857244586749

theorem tailTrace_2057974 : CollatzResearch.WordTrace tailWord_2057974 prefixEnd_2057974 156552568363857244586749 := by
  unfold tailWord_2057974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691279890394946676377311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50040318830879431214691317 4691279890394946676377311)
  ·
    refine ⟨7036919835592420014565967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4691279890394946676377311 7036919835592420014565967)
    ·
      refine ⟨10555379753388630021848951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7036919835592420014565967 10555379753388630021848951)
      ·
        refine ⟨15833069630082945032773427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10555379753388630021848951 15833069630082945032773427)
        ·
          refine ⟨23749604445124417549160141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15833069630082945032773427 23749604445124417549160141)
          ·
            refine ⟨8906101666921656580935053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23749604445124417549160141 8906101666921656580935053)
            ·
              refine ⟨3339788125095621217850645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8906101666921656580935053 3339788125095621217850645)
              ·
                refine ⟨156552568363857244586749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3339788125095621217850645 156552568363857244586749)
                ·
                  rfl

theorem cell21_2057974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_2057974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057974 prefixEnd_2057974 := by exact prefixLift 2057974
  have htrace : WordTrace (prefixWord ++ tailWord_2057974) baseStart_2057974 baseEnd_2057974 := by
    simpa [prefixWord, tailWord_2057974, baseEnd_2057974] using wordTrace_append hprefix tailTrace_2057974
  have hstable : (prefixWord ++ tailWord_2057974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057974).length < 2 ^ (prefixWord ++ tailWord_2057974).sum := by decide
  have hdescent : baseEnd_2057974 < baseStart_2057974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057988 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_2057988 : Nat := 118140960795 + 2057988 * 2 ^ 59
def prefixEnd_2057988 : Nat := 4983230072969 + 3 ^ 40 * 2057988 * 2
def baseEnd_2057988 : Nat := 469660900082310820526885

theorem tailTrace_2057988 : CollatzResearch.WordTrace tailWord_2057988 prefixEnd_2057988 469660900082310820526885 := by
  unfold tailWord_2057988
  simp only [CollatzResearch.WordTrace]
  refine ⟨37530494434134213606523309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50040659245512284808697745 37530494434134213606523309)
  ·
    refine ⟨14073935412800330102446241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37530494434134213606523309 14073935412800330102446241)
    ·
      refine ⟨10555451559600247576834681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14073935412800330102446241 10555451559600247576834681)
      ·
        refine ⟨7916588669700185682626011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10555451559600247576834681 7916588669700185682626011)
        ·
          refine ⟨11874883004550278523939017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7916588669700185682626011 11874883004550278523939017)
          ·
            refine ⟨8906162253412708892954263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11874883004550278523939017 8906162253412708892954263)
            ·
              refine ⟨13359243380119063339431395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906162253412708892954263 13359243380119063339431395)
              ·
                refine ⟨20038865070178595009147093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13359243380119063339431395 20038865070178595009147093)
                ·
                  refine ⟨469660900082310820526885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20038865070178595009147093 469660900082310820526885)
                  ·
                    rfl

theorem cell21_2057988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_2057988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057988 prefixEnd_2057988 := by exact prefixLift 2057988
  have htrace : WordTrace (prefixWord ++ tailWord_2057988) baseStart_2057988 baseEnd_2057988 := by
    simpa [prefixWord, tailWord_2057988, baseEnd_2057988] using wordTrace_append hprefix tailTrace_2057988
  have hstable : (prefixWord ++ tailWord_2057988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057988).length < 2 ^ (prefixWord ++ tailWord_2057988).sum := by decide
  have hdescent : baseEnd_2057988 < baseStart_2057988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2057991 : List Nat := [1, 1, 4, 4, 2, 1, 3, 5]
def baseStart_2057991 : Nat := 118140960795 + 2057991 * 2 ^ 59
def prefixEnd_2057991 : Nat := 4983230072969 + 3 ^ 40 * 2057991 * 2
def baseEnd_2057991 : Nat := 156553861574394493992293

theorem tailTrace_2057991 : CollatzResearch.WordTrace tailWord_2057991 prefixEnd_2057991 156553861574394493992293 := by
  unfold tailWord_2057991
  simp only [CollatzResearch.WordTrace]
  refine ⟨75061098287257558725405827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50040732191505039150270551 75061098287257558725405827)
  ·
    refine ⟨112591647430886338088108741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75061098287257558725405827 112591647430886338088108741)
    ·
      refine ⟨21110933893291188391520389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112591647430886338088108741 21110933893291188391520389)
      ·
        refine ⟨3958300104992097823410073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21110933893291188391520389 3958300104992097823410073)
        ·
          refine ⟨2968725078744073367557555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3958300104992097823410073 2968725078744073367557555)
          ·
            refine ⟨4453087618116110051336333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968725078744073367557555 4453087618116110051336333)
            ·
              refine ⟨1669907856793541269251125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4453087618116110051336333 1669907856793541269251125)
              ·
                refine ⟨156553861574394493992293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1669907856793541269251125 156553861574394493992293)
                ·
                  rfl

theorem cell21_2057991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 5].length) (baseStart_2057991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2057991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2057991 prefixEnd_2057991 := by exact prefixLift 2057991
  have htrace : WordTrace (prefixWord ++ tailWord_2057991) baseStart_2057991 baseEnd_2057991 := by
    simpa [prefixWord, tailWord_2057991, baseEnd_2057991] using wordTrace_append hprefix tailTrace_2057991
  have hstable : (prefixWord ++ tailWord_2057991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2057991).length < 2 ^ (prefixWord ++ tailWord_2057991).sum := by decide
  have hdescent : baseEnd_2057991 < baseStart_2057991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2057991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058005 : List Nat := [1, 3, 2, 1, 2, 3, 1, 5, 3]
def baseStart_2058005 : Nat := 118140960795 + 2058005 * 2 ^ 59
def prefixEnd_2058005 : Nat := 4983230072969 + 3 ^ 40 * 2058005 * 2
def baseEnd_2058005 : Nat := 469664779713922568743517

theorem tailTrace_2058005 : CollatzResearch.WordTrace tailWord_2058005 prefixEnd_2058005 469664779713922568743517 := by
  unfold tailWord_2058005
  simp only [CollatzResearch.WordTrace]
  refine ⟨75061608909206839116415469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50041072606137892744276979 75061608909206839116415469)
  ·
    refine ⟨28148103340952564668655801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75061608909206839116415469 28148103340952564668655801)
    ·
      refine ⟨21111077505714423501491851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28148103340952564668655801 21111077505714423501491851)
      ·
        refine ⟨31666616258571635252237777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21111077505714423501491851 31666616258571635252237777)
        ·
          refine ⟨23749962193928726439178333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31666616258571635252237777 23749962193928726439178333)
          ·
            refine ⟨8906235822723272414691875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23749962193928726439178333 8906235822723272414691875)
            ·
              refine ⟨13359353734084908622037813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8906235822723272414691875 13359353734084908622037813)
              ·
                refine ⟨1252439412570460183316045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13359353734084908622037813 1252439412570460183316045)
                ·
                  refine ⟨469664779713922568743517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252439412570460183316045 469664779713922568743517)
                  ·
                    rfl

theorem cell21_2058005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_2058005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058005 prefixEnd_2058005 := by exact prefixLift 2058005
  have htrace : WordTrace (prefixWord ++ tailWord_2058005) baseStart_2058005 baseEnd_2058005 := by
    simpa [prefixWord, tailWord_2058005, baseEnd_2058005] using wordTrace_append hprefix tailTrace_2058005
  have hstable : (prefixWord ++ tailWord_2058005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058005).length < 2 ^ (prefixWord ++ tailWord_2058005).sum := by decide
  have hdescent : baseEnd_2058005 < baseStart_2058005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058019 : List Nat := [1, 1, 1, 4, 2, 1, 5, 2, 4]
def baseStart_2058019 : Nat := 118140960795 + 2058019 * 2 ^ 59
def prefixEnd_2058019 : Nat := 4983230072969 + 3 ^ 40 * 2058019 * 2
def baseEnd_2058019 : Nat := 469667974704661655510155

theorem tailTrace_2058019 : CollatzResearch.WordTrace tailWord_2058019 prefixEnd_2058019 469667974704661655510155 := by
  unfold tailWord_2058019
  simp only [CollatzResearch.WordTrace]
  refine ⟨75062119531156119507425111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50041413020770746338283407 75062119531156119507425111)
  ·
    refine ⟨112593179296734179261137667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75062119531156119507425111 112593179296734179261137667)
    ·
      refine ⟨168889768945101268891706501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112593179296734179261137667 168889768945101268891706501)
      ·
        refine ⟨31666831677206487917194969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168889768945101268891706501 31666831677206487917194969)
        ·
          refine ⟨23750123757904865937896227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31666831677206487917194969 23750123757904865937896227)
          ·
            refine ⟨35625185636857298906844341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23750123757904865937896227 35625185636857298906844341)
            ·
              refine ⟨3339861153455371772516657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35625185636857298906844341 3339861153455371772516657)
              ·
                refine ⟨2504895865091528829387493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3339861153455371772516657 2504895865091528829387493)
                ·
                  refine ⟨469667974704661655510155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2504895865091528829387493 469667974704661655510155)
                  ·
                    rfl

theorem cell21_2058019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 4].length) (baseStart_2058019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058019 prefixEnd_2058019 := by exact prefixLift 2058019
  have htrace : WordTrace (prefixWord ++ tailWord_2058019) baseStart_2058019 baseEnd_2058019 := by
    simpa [prefixWord, tailWord_2058019, baseEnd_2058019] using wordTrace_append hprefix tailTrace_2058019
  have hstable : (prefixWord ++ tailWord_2058019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058019).length < 2 ^ (prefixWord ++ tailWord_2058019).sum := by decide
  have hdescent : baseEnd_2058019 < baseStart_2058019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058126 : List Nat := [4, 1, 1, 5, 1, 9]
def baseStart_2058126 : Nat := 118140960795 + 2058126 * 2 ^ 59
def prefixEnd_2058126 : Nat := 4983230072969 + 3 ^ 40 * 2058126 * 2
def baseEnd_2058126 : Nat := 17396014576387157304689

theorem tailTrace_2058126 : CollatzResearch.WordTrace tailWord_2058126 prefixEnd_2058126 17396014576387157304689 := by
  unfold tailWord_2058126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383252767721059597696279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50044014761178984521046821 9383252767721059597696279)
  ·
    refine ⟨14074879151581589396544419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9383252767721059597696279 14074879151581589396544419)
    ·
      refine ⟨21112318727372384094816629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14074879151581589396544419 21112318727372384094816629)
      ·
        refine ⟨1979279880691161008889059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21112318727372384094816629 1979279880691161008889059)
        ·
          refine ⟨2968919821036741513333589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979279880691161008889059 2968919821036741513333589)
          ·
            refine ⟨17396014576387157304689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2968919821036741513333589 17396014576387157304689)
            ·
              rfl

theorem cell21_2058126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 9].length) (baseStart_2058126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058126 prefixEnd_2058126 := by exact prefixLift 2058126
  have htrace : WordTrace (prefixWord ++ tailWord_2058126) baseStart_2058126 baseEnd_2058126 := by
    simpa [prefixWord, tailWord_2058126, baseEnd_2058126] using wordTrace_append hprefix tailTrace_2058126
  have hstable : (prefixWord ++ tailWord_2058126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058126).length < 2 ^ (prefixWord ++ tailWord_2058126).sum := by decide
  have hdescent : baseEnd_2058126 < baseStart_2058126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058143 : List Nat := [1, 1, 2, 5, 4, 1, 1, 6]
def baseStart_2058143 : Nat := 118140960795 + 2058143 * 2 ^ 59
def prefixEnd_2058143 : Nat := 4983230072969 + 3 ^ 40 * 2058143 * 2
def baseEnd_2058143 : Nat := 156565424398021665147745

theorem tailTrace_2058143 : CollatzResearch.WordTrace tailWord_2058143 prefixEnd_2058143 156565424398021665147745 := by
  unfold tailWord_2058143
  simp only [CollatzResearch.WordTrace]
  refine ⟨75066642182706888684939083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50044428121804592456626055 75066642182706888684939083)
  ·
    refine ⟨112599963274060333027408625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75066642182706888684939083 112599963274060333027408625)
    ·
      refine ⟨84449972455545249770556469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112599963274060333027408625 84449972455545249770556469)
      ·
        refine ⟨7917184917707367165989669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84449972455545249770556469 7917184917707367165989669)
        ·
          refine ⟨1484472172070131343623063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7917184917707367165989669 1484472172070131343623063)
          ·
            refine ⟨2226708258105197015434595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484472172070131343623063 2226708258105197015434595)
            ·
              refine ⟨3340062387157795523151893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226708258105197015434595 3340062387157795523151893)
              ·
                refine ⟨156565424398021665147745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3340062387157795523151893 156565424398021665147745)
                ·
                  rfl

theorem cell21_2058143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 6].length) (baseStart_2058143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058143 prefixEnd_2058143 := by exact prefixLift 2058143
  have htrace : WordTrace (prefixWord ++ tailWord_2058143) baseStart_2058143 baseEnd_2058143 := by
    simpa [prefixWord, tailWord_2058143, baseEnd_2058143] using wordTrace_append hprefix tailTrace_2058143
  have hstable : (prefixWord ++ tailWord_2058143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058143).length < 2 ^ (prefixWord ++ tailWord_2058143).sum := by decide
  have hdescent : baseEnd_2058143 < baseStart_2058143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058174 : List Nat := [4, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2058174 : Nat := 118140960795 + 2058174 * 2 ^ 59
def prefixEnd_2058174 : Nat := 4983230072969 + 3 ^ 40 * 2058174 * 2
def baseEnd_2058174 : Nat := 469703347816415830426505

theorem tailTrace_2058174 : CollatzResearch.WordTrace tailWord_2058174 prefixEnd_2058174 469703347816415830426505 := by
  unfold tailWord_2058174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9383471605699322622414697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50045181897063053986211717 9383471605699322622414697)
  ·
    refine ⟨7037603704274491966811023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9383471605699322622414697 7037603704274491966811023)
    ·
      refine ⟨10556405556411737950216535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7037603704274491966811023 10556405556411737950216535)
      ·
        refine ⟨15834608334617606925324803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10556405556411737950216535 15834608334617606925324803)
        ·
          refine ⟨23751912501926410387987205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15834608334617606925324803 23751912501926410387987205)
          ·
            refine ⟨4453483594111201947747601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23751912501926410387987205 4453483594111201947747601)
            ·
              refine ⟨3340112695583401460810701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4453483594111201947747601 3340112695583401460810701)
              ·
                refine ⟨1252542260843775547804013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3340112695583401460810701 1252542260843775547804013)
                ·
                  refine ⟨469703347816415830426505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252542260843775547804013 469703347816415830426505)
                  ·
                    rfl

theorem cell21_2058174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2058174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058174 prefixEnd_2058174 := by exact prefixLift 2058174
  have htrace : WordTrace (prefixWord ++ tailWord_2058174) baseStart_2058174 baseEnd_2058174 := by
    simpa [prefixWord, tailWord_2058174, baseEnd_2058174] using wordTrace_append hprefix tailTrace_2058174
  have hstable : (prefixWord ++ tailWord_2058174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058174).length < 2 ^ (prefixWord ++ tailWord_2058174).sum := by decide
  have hdescent : baseEnd_2058174 < baseStart_2058174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058188 : List Nat := [2, 2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_2058188 : Nat := 118140960795 + 2058188 * 2 ^ 59
def prefixEnd_2058188 : Nat := 4983230072969 + 3 ^ 40 * 2058188 * 2
def baseEnd_2058188 : Nat := 469706542807154917193143

theorem tailTrace_2058188 : CollatzResearch.WordTrace tailWord_2058188 prefixEnd_2058188 469706542807154917193143 := by
  unfold tailWord_2058188
  simp only [CollatzResearch.WordTrace]
  refine ⟨37534141733771930685163609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50045522311695907580218145 37534141733771930685163609)
  ·
    refine ⟨28150606300328948013872707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37534141733771930685163609 28150606300328948013872707)
    ·
      refine ⟨42225909450493422020809061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28150606300328948013872707 42225909450493422020809061)
      ·
        refine ⟨7917358021967516628901699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42225909450493422020809061 7917358021967516628901699)
        ·
          refine ⟨11876037032951274943352549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7917358021967516628901699 11876037032951274943352549)
          ·
            refine ⟨2226756943678364051878603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11876037032951274943352549 2226756943678364051878603)
            ·
              refine ⟨3340135415517546077817905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226756943678364051878603 3340135415517546077817905)
              ·
                refine ⟨2505101561638159558363429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340135415517546077817905 2505101561638159558363429)
                ·
                  refine ⟨469706542807154917193143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2505101561638159558363429 469706542807154917193143)
                  ·
                    rfl

theorem cell21_2058188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_2058188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058188 prefixEnd_2058188 := by exact prefixLift 2058188
  have htrace : WordTrace (prefixWord ++ tailWord_2058188) baseStart_2058188 baseEnd_2058188 := by
    simpa [prefixWord, tailWord_2058188, baseEnd_2058188] using wordTrace_append hprefix tailTrace_2058188
  have hstable : (prefixWord ++ tailWord_2058188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058188).length < 2 ^ (prefixWord ++ tailWord_2058188).sum := by decide
  have hdescent : baseEnd_2058188 < baseStart_2058188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058205 : List Nat := [1, 4, 3, 1, 3, 1, 3, 1, 4]
def baseStart_2058205 : Nat := 118140960795 + 2058205 * 2 ^ 59
def prefixEnd_2058205 : Nat := 4983230072969 + 3 ^ 40 * 2058205 * 2
def baseEnd_2058205 : Nat := 469710422438766665409775

theorem tailTrace_2058205 : CollatzResearch.WordTrace tailWord_2058205 prefixEnd_2058205 469710422438766665409775 := by
  unfold tailWord_2058205
  simp only [CollatzResearch.WordTrace]
  refine ⟨75068903508482273273696069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50045935672321515515797379 75068903508482273273696069)
  ·
    refine ⟨14075419407840426238818013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75068903508482273273696069 14075419407840426238818013)
    ·
      refine ⟨5278282277940159839556755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14075419407840426238818013 5278282277940159839556755)
      ·
        refine ⟨7917423416910239759335133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278282277940159839556755 7917423416910239759335133)
        ·
          refine ⟨2969033781341339909750675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7917423416910239759335133 2969033781341339909750675)
          ·
            refine ⟨4453550672012009864626013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969033781341339909750675 4453550672012009864626013)
            ·
              refine ⟨1670081502004503699234755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4453550672012009864626013 1670081502004503699234755)
              ·
                refine ⟨2505122253006755548852133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670081502004503699234755 2505122253006755548852133)
                ·
                  refine ⟨469710422438766665409775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2505122253006755548852133 469710422438766665409775)
                  ·
                    rfl

theorem cell21_2058205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_2058205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058205 prefixEnd_2058205 := by exact prefixLift 2058205
  have htrace : WordTrace (prefixWord ++ tailWord_2058205) baseStart_2058205 baseEnd_2058205 := by
    simpa [prefixWord, tailWord_2058205, baseEnd_2058205] using wordTrace_append hprefix tailTrace_2058205
  have hstable : (prefixWord ++ tailWord_2058205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058205).length < 2 ^ (prefixWord ++ tailWord_2058205).sum := by decide
  have hdescent : baseEnd_2058205 < baseStart_2058205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058233 : List Nat := [1, 2, 1, 3, 1, 4, 3, 3, 3]
def baseStart_2058233 : Nat := 118140960795 + 2058233 * 2 ^ 59
def prefixEnd_2058233 : Nat := 4983230072969 + 3 ^ 40 * 2058233 * 2
def baseEnd_2058233 : Nat := 469716812420244838943051

theorem tailTrace_2058233 : CollatzResearch.WordTrace tailWord_2058233 prefixEnd_2058233 469716812420244838943051 := by
  unfold tailWord_2058233
  simp only [CollatzResearch.WordTrace]
  refine ⟨75069924752380834055715353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50046616501587222703810235 75069924752380834055715353)
  ·
    refine ⟨56302443564285625541786515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75069924752380834055715353 56302443564285625541786515)
    ·
      refine ⟨84453665346428438312679773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56302443564285625541786515 84453665346428438312679773)
      ·
        refine ⟨31670124504910664367254915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84453665346428438312679773 31670124504910664367254915)
        ·
          refine ⟨47505186757365996550882373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31670124504910664367254915 47505186757365996550882373)
          ·
            refine ⟨8907222517006124353290445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47505186757365996550882373 8907222517006124353290445)
            ·
              refine ⟨3340208443877296632483917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8907222517006124353290445 3340208443877296632483917)
              ·
                refine ⟨1252578166453986237181469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3340208443877296632483917 1252578166453986237181469)
                ·
                  refine ⟨469716812420244838943051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252578166453986237181469 469716812420244838943051)
                  ·
                    rfl

theorem cell21_2058233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 3].length) (baseStart_2058233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058233 prefixEnd_2058233 := by exact prefixLift 2058233
  have htrace : WordTrace (prefixWord ++ tailWord_2058233) baseStart_2058233 baseEnd_2058233 := by
    simpa [prefixWord, tailWord_2058233, baseEnd_2058233] using wordTrace_append hprefix tailTrace_2058233
  have hstable : (prefixWord ++ tailWord_2058233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058233).length < 2 ^ (prefixWord ++ tailWord_2058233).sum := by decide
  have hdescent : baseEnd_2058233 < baseStart_2058233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058250 : List Nat := [3, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_2058250 : Nat := 118140960795 + 2058250 * 2 ^ 59
def prefixEnd_2058250 : Nat := 4983230072969 + 3 ^ 40 * 2058250 * 2
def baseEnd_2058250 : Nat := 469720692051856587159683

theorem tailTrace_2058250 : CollatzResearch.WordTrace tailWord_2058250 prefixEnd_2058250 469720692051856587159683 := by
  unfold tailWord_2058250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18767636198329811489771051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50047029862212830639389469 18767636198329811489771051)
  ·
    refine ⟨28151454297494717234656577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18767636198329811489771051 28151454297494717234656577)
    ·
      refine ⟨21113590723121037925992433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28151454297494717234656577 21113590723121037925992433)
      ·
        refine ⟨15835193042340778444494325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21113590723121037925992433 15835193042340778444494325)
        ·
          refine ⟨1484549347719447979171343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15835193042340778444494325 1484549347719447979171343)
          ·
            refine ⟨2226824021579171968757015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484549347719447979171343 2226824021579171968757015)
            ·
              refine ⟨3340236032368757953135523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2226824021579171968757015 3340236032368757953135523)
              ·
                refine ⟨5010354048553136929703285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3340236032368757953135523 5010354048553136929703285)
                ·
                  refine ⟨469720692051856587159683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5010354048553136929703285 469720692051856587159683)
                  ·
                    rfl

theorem cell21_2058250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_2058250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058250 prefixEnd_2058250 := by exact prefixLift 2058250
  have htrace : WordTrace (prefixWord ++ tailWord_2058250) baseStart_2058250 baseEnd_2058250 := by
    simpa [prefixWord, tailWord_2058250, baseEnd_2058250] using wordTrace_append hprefix tailTrace_2058250
  have hstable : (prefixWord ++ tailWord_2058250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058250).length < 2 ^ (prefixWord ++ tailWord_2058250).sum := by decide
  have hdescent : baseEnd_2058250 < baseStart_2058250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058275 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 7]
def baseStart_2058275 : Nat := 118140960795 + 2058275 * 2 ^ 59
def prefixEnd_2058275 : Nat := 4983230072969 + 3 ^ 40 * 2058275 * 2
def baseEnd_2058275 : Nat := 469726397392462099242965

theorem tailTrace_2058275 : CollatzResearch.WordTrace tailWord_2058275 prefixEnd_2058275 469726397392462099242965 := by
  unfold tailWord_2058275
  simp only [CollatzResearch.WordTrace]
  refine ⟨75071456618228675228744279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50047637745485783485829519 75071456618228675228744279)
  ·
    refine ⟨112607184927343012843116419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75071456618228675228744279 112607184927343012843116419)
    ·
      refine ⟨168910777391014519264674629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112607184927343012843116419 168910777391014519264674629)
      ·
        refine ⟨31670770760815222362126493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168910777391014519264674629 31670770760815222362126493)
        ·
          refine ⟨11876539035305708385797435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31670770760815222362126493 11876539035305708385797435)
          ·
            refine ⟨17814808552958562578696153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11876539035305708385797435 17814808552958562578696153)
            ·
              refine ⟨13361106414718921934022115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17814808552958562578696153 13361106414718921934022115)
              ·
                refine ⟨20041659622078382901033173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13361106414718921934022115 20041659622078382901033173)
                ·
                  refine ⟨469726397392462099242965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20041659622078382901033173 469726397392462099242965)
                  ·
                    rfl

theorem cell21_2058275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_2058275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058275 prefixEnd_2058275 := by exact prefixLift 2058275
  have htrace : WordTrace (prefixWord ++ tailWord_2058275) baseStart_2058275 baseEnd_2058275 := by
    simpa [prefixWord, tailWord_2058275, baseEnd_2058275] using wordTrace_append hprefix tailTrace_2058275
  have hstable : (prefixWord ++ tailWord_2058275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058275).length < 2 ^ (prefixWord ++ tailWord_2058275).sum := by decide
  have hdescent : baseEnd_2058275 < baseStart_2058275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058326 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2058326 : Nat := 118140960795 + 2058326 * 2 ^ 59
def prefixEnd_2058326 : Nat := 4983230072969 + 3 ^ 40 * 2058326 * 2
def baseEnd_2058326 : Nat := 469738036287297343892861

theorem tailTrace_2058326 : CollatzResearch.WordTrace tailWord_2058326 prefixEnd_2058326 469738036287297343892861 := by
  unfold tailWord_2058326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4692082296315244433678177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50048877827362607292567221 4692082296315244433678177)
  ·
    refine ⟨3519061722236433325258633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4692082296315244433678177 3519061722236433325258633)
    ·
      refine ⟨2639296291677324993943975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3519061722236433325258633 2639296291677324993943975)
      ·
        refine ⟨3958944437515987490915963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2639296291677324993943975 3958944437515987490915963)
        ·
          refine ⟨5938416656273981236373945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3958944437515987490915963 5938416656273981236373945)
          ·
            refine ⟨4453812492205485927280459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5938416656273981236373945 4453812492205485927280459)
            ·
              refine ⟨6680718738308228890920689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453812492205485927280459 6680718738308228890920689)
              ·
                refine ⟨5010539053731171668190517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6680718738308228890920689 5010539053731171668190517)
                ·
                  refine ⟨469738036287297343892861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5010539053731171668190517 469738036287297343892861)
                  ·
                    rfl

theorem cell21_2058326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2058326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058326 prefixEnd_2058326 := by exact prefixLift 2058326
  have htrace : WordTrace (prefixWord ++ tailWord_2058326) baseStart_2058326 baseEnd_2058326 := by
    simpa [prefixWord, tailWord_2058326, baseEnd_2058326] using wordTrace_append hprefix tailTrace_2058326
  have hstable : (prefixWord ++ tailWord_2058326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058326).length < 2 ^ (prefixWord ++ tailWord_2058326).sum := by decide
  have hdescent : baseEnd_2058326 < baseStart_2058326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058388 : List Nat := [2, 4, 2, 3, 1, 2, 2, 5]
def baseStart_2058388 : Nat := 118140960795 + 2058388 * 2 ^ 59
def prefixEnd_2058388 : Nat := 4983230072969 + 3 ^ 40 * 2058388 * 2
def baseEnd_2058388 : Nat := 156584061843999671286467

theorem tailTrace_2058388 : CollatzResearch.WordTrace tailWord_2058388 prefixEnd_2058388 156584061843999671286467 := by
  unfold tailWord_2058388
  simp only [CollatzResearch.WordTrace]
  refine ⟨37537789033409647763803909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50050385377879530351738545 37537789033409647763803909)
  ·
    refine ⟨7038335443764308955713233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37537789033409647763803909 7038335443764308955713233)
    ·
      refine ⟨5278751582823231716784925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7038335443764308955713233 5278751582823231716784925)
      ·
        refine ⟨1979531843558711893794347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5278751582823231716784925 1979531843558711893794347)
        ·
          refine ⟨2969297765338067840691521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979531843558711893794347 2969297765338067840691521)
          ·
            refine ⟨2226973324003550880518641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2969297765338067840691521 2226973324003550880518641)
            ·
              refine ⟨1670229993002663160388981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2226973324003550880518641 1670229993002663160388981)
              ·
                refine ⟨156584061843999671286467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1670229993002663160388981 156584061843999671286467)
                ·
                  rfl

theorem cell21_2058388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_2058388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058388 prefixEnd_2058388 := by exact prefixLift 2058388
  have htrace : WordTrace (prefixWord ++ tailWord_2058388) baseStart_2058388 baseEnd_2058388 := by
    simpa [prefixWord, tailWord_2058388, baseEnd_2058388] using wordTrace_append hprefix tailTrace_2058388
  have hstable : (prefixWord ++ tailWord_2058388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058388).length < 2 ^ (prefixWord ++ tailWord_2058388).sum := by decide
  have hdescent : baseEnd_2058388 < baseStart_2058388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058402 : List Nat := [3, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_2058402 : Nat := 118140960795 + 2058402 * 2 ^ 59
def prefixEnd_2058402 : Nat := 4983230072969 + 3 ^ 40 * 2058402 * 2
def baseEnd_2058402 : Nat := 469755380522738100626039

theorem tailTrace_2058402 : CollatzResearch.WordTrace tailWord_2058402 prefixEnd_2058402 469755380522738100626039 := by
  unfold tailWord_2058402
  simp only [CollatzResearch.WordTrace]
  refine ⟨18769022172192143979654365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50050725792512383945744973 18769022172192143979654365)
  ·
    refine ⟨7038383314572053992370387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18769022172192143979654365 7038383314572053992370387)
    ·
      refine ⟨10557574971858080988555581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7038383314572053992370387 10557574971858080988555581)
      ·
        refine ⟨3959090614446780370708343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10557574971858080988555581 3959090614446780370708343)
        ·
          refine ⟨5938635921670170556062515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3959090614446780370708343 5938635921670170556062515)
          ·
            refine ⟨8907953882505255834093773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938635921670170556062515 8907953882505255834093773)
            ·
              refine ⟨3340482705939470937785165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8907953882505255834093773 3340482705939470937785165)
              ·
                refine ⟨1252681014727301601669437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3340482705939470937785165 1252681014727301601669437)
                ·
                  refine ⟨469755380522738100626039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252681014727301601669437 469755380522738100626039)
                  ·
                    rfl

theorem cell21_2058402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_2058402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058402 prefixEnd_2058402 := by exact prefixLift 2058402
  have htrace : WordTrace (prefixWord ++ tailWord_2058402) baseStart_2058402 baseEnd_2058402 := by
    simpa [prefixWord, tailWord_2058402, baseEnd_2058402] using wordTrace_append hprefix tailTrace_2058402
  have hstable : (prefixWord ++ tailWord_2058402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058402).length < 2 ^ (prefixWord ++ tailWord_2058402).sum := by decide
  have hdescent : baseEnd_2058402 < baseStart_2058402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058413 : List Nat := [1, 5, 2, 1, 2, 1, 9]
def baseStart_2058413 : Nat := 118140960795 + 2058413 * 2 ^ 59
def prefixEnd_2058413 : Nat := 4983230072969 + 3 ^ 40 * 2058413 * 2
def baseEnd_2058413 : Nat := 52195321208067169549187

theorem tailTrace_2058413 : CollatzResearch.WordTrace tailWord_2058413 prefixEnd_2058413 52195321208067169549187 := by
  unfold tailWord_2058413
  simp only [CollatzResearch.WordTrace]
  refine ⟨75076489891728724797267893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50050993261152483198178595 75076489891728724797267893)
  ·
    refine ⟨7038420927349567949743865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75076489891728724797267893 7038420927349567949743865)
    ·
      refine ⟨5278815695512175962307899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7038420927349567949743865 5278815695512175962307899)
      ·
        refine ⟨7918223543268263943461849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5278815695512175962307899 7918223543268263943461849)
        ·
          refine ⟨5938667657451197957596387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7918223543268263943461849 5938667657451197957596387)
          ·
            refine ⟨8908001486176796936394581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5938667657451197957596387 8908001486176796936394581)
            ·
              refine ⟨52195321208067169549187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8908001486176796936394581 52195321208067169549187)
              ·
                rfl

theorem cell21_2058413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 9].length) (baseStart_2058413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058413 prefixEnd_2058413 := by exact prefixLift 2058413
  have htrace : WordTrace (prefixWord ++ tailWord_2058413) baseStart_2058413 baseEnd_2058413 := by
    simpa [prefixWord, tailWord_2058413, baseEnd_2058413] using wordTrace_append hprefix tailTrace_2058413
  have hstable : (prefixWord ++ tailWord_2058413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058413).length < 2 ^ (prefixWord ++ tailWord_2058413).sum := by decide
  have hdescent : baseEnd_2058413 < baseStart_2058413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058430 : List Nat := [4, 2, 1, 1, 4, 1, 2, 6]
def baseStart_2058430 : Nat := 118140960795 + 2058430 * 2 ^ 59
def prefixEnd_2058430 : Nat := 4983230072969 + 3 ^ 40 * 2058430 * 2
def baseEnd_2058430 : Nat := 156587256834738758053105

theorem tailTrace_2058430 : CollatzResearch.WordTrace tailWord_2058430 prefixEnd_2058430 156587256834738758053105 := by
  unfold tailWord_2058430
  simp only [CollatzResearch.WordTrace]
  refine ⟨9384638741583392087579593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50051406621778091133757829 9384638741583392087579593)
  ·
    refine ⟨7038479056187544065684695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9384638741583392087579593 7038479056187544065684695)
    ·
      refine ⟨10557718584281316098527043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7038479056187544065684695 10557718584281316098527043)
      ·
        refine ⟨15836577876421974147790565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10557718584281316098527043 15836577876421974147790565)
        ·
          refine ⟨2969358351829120152710731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15836577876421974147790565 2969358351829120152710731)
          ·
            refine ⟨4454037527743680229066097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969358351829120152710731 4454037527743680229066097)
            ·
              refine ⟨3340528145807760171799573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4454037527743680229066097 3340528145807760171799573)
              ·
                refine ⟨156587256834738758053105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3340528145807760171799573 156587256834738758053105)
                ·
                  rfl

theorem cell21_2058430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_2058430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058430 prefixEnd_2058430 := by exact prefixLift 2058430
  have htrace : WordTrace (prefixWord ++ tailWord_2058430) baseStart_2058430 baseEnd_2058430 := by
    simpa [prefixWord, tailWord_2058430, baseEnd_2058430] using wordTrace_append hprefix tailTrace_2058430
  have hstable : (prefixWord ++ tailWord_2058430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058430).length < 2 ^ (prefixWord ++ tailWord_2058430).sum := by decide
  have hdescent : baseEnd_2058430 < baseStart_2058430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058441 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 8]
def baseStart_2058441 : Nat := 118140960795 + 2058441 * 2 ^ 59
def prefixEnd_2058441 : Nat := 4983230072969 + 3 ^ 40 * 2058441 * 2
def baseEnd_2058441 : Nat := 469764280854082699475959

theorem tailTrace_2058441 : CollatzResearch.WordTrace tailWord_2058441 prefixEnd_2058441 469764280854082699475959 := by
  unfold tailWord_2058441
  simp only [CollatzResearch.WordTrace]
  refine ⟨75077511135627285579287177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50051674090418190386191451 75077511135627285579287177)
  ·
    refine ⟨56308133351720464184465383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75077511135627285579287177 56308133351720464184465383)
    ·
      refine ⟨84462200027580696276698075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56308133351720464184465383 84462200027580696276698075)
      ·
        refine ⟨126693300041371044415047113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84462200027580696276698075 126693300041371044415047113)
        ·
          refine ⟨95019975031028283311285335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126693300041371044415047113 95019975031028283311285335)
          ·
            refine ⟨142529962546542424966928003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95019975031028283311285335 142529962546542424966928003)
            ·
              refine ⟨213794943819813637450392005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142529962546542424966928003 213794943819813637450392005)
              ·
                refine ⟨40086551966215057021948501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213794943819813637450392005 40086551966215057021948501)
                ·
                  refine ⟨469764280854082699475959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40086551966215057021948501 469764280854082699475959)
                  ·
                    rfl

theorem cell21_2058441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_2058441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058441 prefixEnd_2058441 := by exact prefixLift 2058441
  have htrace : WordTrace (prefixWord ++ tailWord_2058441) baseStart_2058441 baseEnd_2058441 := by
    simpa [prefixWord, tailWord_2058441, baseEnd_2058441] using wordTrace_append hprefix tailTrace_2058441
  have hstable : (prefixWord ++ tailWord_2058441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058441).length < 2 ^ (prefixWord ++ tailWord_2058441).sum := by decide
  have hdescent : baseEnd_2058441 < baseStart_2058441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058472 : List Nat := [2, 1, 4, 1, 2, 11]
def baseStart_2058472 : Nat := 118140960795 + 2058472 * 2 ^ 59
def prefixEnd_2058472 : Nat := 4983230072969 + 3 ^ 40 * 2058472 * 2
def baseEnd_2058472 : Nat := 17398939091719760535527

theorem tailTrace_2058472 : CollatzResearch.WordTrace tailWord_2058472 prefixEnd_2058472 17398939091719760535527 := by
  unfold tailWord_2058472
  simp only [CollatzResearch.WordTrace]
  refine ⟨37539320899257488936832835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50052427865676651915777113 37539320899257488936832835)
  ·
    refine ⟨56308981348886233405249253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37539320899257488936832835 56308981348886233405249253)
    ·
      refine ⟨10557934002916168763484235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56308981348886233405249253 10557934002916168763484235)
      ·
        refine ⟨15836901004374253145226353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10557934002916168763484235 15836901004374253145226353)
        ·
          refine ⟨11877675753280689858919765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15836901004374253145226353 11877675753280689858919765)
          ·
            refine ⟨17398939091719760535527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11877675753280689858919765 17398939091719760535527)
            ·
              rfl

theorem cell21_2058472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 11].length) (baseStart_2058472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058472 prefixEnd_2058472 := by exact prefixLift 2058472
  have htrace : WordTrace (prefixWord ++ tailWord_2058472) baseStart_2058472 baseEnd_2058472 := by
    simpa [prefixWord, tailWord_2058472, baseEnd_2058472] using wordTrace_append hprefix tailTrace_2058472
  have hstable : (prefixWord ++ tailWord_2058472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058472).length < 2 ^ (prefixWord ++ tailWord_2058472).sum := by decide
  have hdescent : baseEnd_2058472 < baseStart_2058472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058644 : List Nat := [2, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2058644 : Nat := 118140960795 + 2058644 * 2 ^ 59
def prefixEnd_2058644 : Nat := 4983230072969 + 3 ^ 40 * 2058644 * 2
def baseEnd_2058644 : Nat := 469810608219799457592211

theorem tailTrace_2058644 : CollatzResearch.WordTrace tailWord_2058644 prefixEnd_2058644 469810608219799457592211 := by
  unfold tailWord_2058644
  simp only [CollatzResearch.WordTrace]
  refine ⟨37542457576945925624463493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50056610102594567499284657 37542457576945925624463493)
  ·
    refine ⟨7039210795677361054586905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37542457576945925624463493 7039210795677361054586905)
    ·
      refine ⟨5279408096758020790940179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7039210795677361054586905 5279408096758020790940179)
      ·
        refine ⟨7919112145137031186410269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5279408096758020790940179 7919112145137031186410269)
        ·
          refine ⟨2969667054426386694903851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7919112145137031186410269 2969667054426386694903851)
          ·
            refine ⟨4454500581639580042355777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969667054426386694903851 4454500581639580042355777)
            ·
              refine ⟨3340875436229685031766833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4454500581639580042355777 3340875436229685031766833)
              ·
                refine ⟨2505656577172263773825125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3340875436229685031766833 2505656577172263773825125)
                ·
                  refine ⟨469810608219799457592211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2505656577172263773825125 469810608219799457592211)
                  ·
                    rfl

theorem cell21_2058644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2058644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058644 prefixEnd_2058644 := by exact prefixLift 2058644
  have htrace : WordTrace (prefixWord ++ tailWord_2058644) baseStart_2058644 baseEnd_2058644 := by
    simpa [prefixWord, tailWord_2058644, baseEnd_2058644] using wordTrace_append hprefix tailTrace_2058644
  have hstable : (prefixWord ++ tailWord_2058644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058644).length < 2 ^ (prefixWord ++ tailWord_2058644).sum := by decide
  have hdescent : baseEnd_2058644 < baseStart_2058644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058655 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 5]
def baseStart_2058655 : Nat := 118140960795 + 2058655 * 2 ^ 59
def prefixEnd_2058655 : Nat := 4983230072969 + 3 ^ 40 * 2058655 * 2
def baseEnd_2058655 : Nat := 469813118569665882908855

theorem tailTrace_2058655 : CollatzResearch.WordTrace tailWord_2058655 prefixEnd_2058655 469813118569665882908855 := by
  unfold tailWord_2058655
  simp only [CollatzResearch.WordTrace]
  refine ⟨75085316356852000127577419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50056877571234666751718279 75085316356852000127577419)
  ·
    refine ⟨112627974535278000191366129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75085316356852000127577419 112627974535278000191366129)
    ·
      refine ⟨84470980901458500143524597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112627974535278000191366129 84470980901458500143524597)
      ·
        refine ⟨7919154459511734388455431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84470980901458500143524597 7919154459511734388455431)
        ·
          refine ⟨11878731689267601582683147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7919154459511734388455431 11878731689267601582683147)
          ·
            refine ⟨17818097533901402374024721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11878731689267601582683147 17818097533901402374024721)
            ·
              refine ⟨13363573150426051780518541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17818097533901402374024721 13363573150426051780518541)
              ·
                refine ⟨5011339931409769417694453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13363573150426051780518541 5011339931409769417694453)
                ·
                  refine ⟨469813118569665882908855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5011339931409769417694453 469813118569665882908855)
                  ·
                    rfl

theorem cell21_2058655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_2058655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058655 prefixEnd_2058655 := by exact prefixLift 2058655
  have htrace : WordTrace (prefixWord ++ tailWord_2058655) baseStart_2058655 baseEnd_2058655 := by
    simpa [prefixWord, tailWord_2058655, baseEnd_2058655] using wordTrace_append hprefix tailTrace_2058655
  have hstable : (prefixWord ++ tailWord_2058655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058655).length < 2 ^ (prefixWord ++ tailWord_2058655).sum := by decide
  have hdescent : baseEnd_2058655 < baseStart_2058655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058734 : List Nat := [4, 1, 2, 1, 2, 4, 2, 5]
def baseStart_2058734 : Nat := 118140960795 + 2058734 * 2 ^ 59
def prefixEnd_2058734 : Nat := 4983230072969 + 3 ^ 40 * 2058734 * 2
def baseEnd_2058734 : Nat := 156610382481993100364009

theorem tailTrace_2058734 : CollatzResearch.WordTrace tailWord_2058734 prefixEnd_2058734 156610382481993100364009 := by
  unfold tailWord_2058734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9386024715445724577462907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50058798482377197746468837 9386024715445724577462907)
  ·
    refine ⟨14079037073168586866194361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9386024715445724577462907 14079037073168586866194361)
    ·
      refine ⟨10559277804876440149645771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14079037073168586866194361 10559277804876440149645771)
      ·
        refine ⟨15838916707314660224468657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10559277804876440149645771 15838916707314660224468657)
        ·
          refine ⟨11879187530485995168351493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15838916707314660224468657 11879187530485995168351493)
          ·
            refine ⟨2227347661966124094065905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11879187530485995168351493 2227347661966124094065905)
            ·
              refine ⟨1670510746474593070549429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227347661966124094065905 1670510746474593070549429)
              ·
                refine ⟨156610382481993100364009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1670510746474593070549429 156610382481993100364009)
                ·
                  rfl

theorem cell21_2058734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_2058734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058734 prefixEnd_2058734 := by exact prefixLift 2058734
  have htrace : WordTrace (prefixWord ++ tailWord_2058734) baseStart_2058734 baseEnd_2058734 := by
    simpa [prefixWord, tailWord_2058734, baseEnd_2058734] using wordTrace_append hprefix tailTrace_2058734
  have hstable : (prefixWord ++ tailWord_2058734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058734).length < 2 ^ (prefixWord ++ tailWord_2058734).sum := by decide
  have hdescent : baseEnd_2058734 < baseStart_2058734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058745 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 6]
def baseStart_2058745 : Nat := 118140960795 + 2058745 * 2 ^ 59
def prefixEnd_2058745 : Nat := 4983230072969 + 3 ^ 40 * 2058745 * 2
def baseEnd_2058745 : Nat := 469833657795845726408671

theorem tailTrace_2058745 : CollatzResearch.WordTrace tailWord_2058745 prefixEnd_2058745 469833657795845726408671 := by
  unfold tailWord_2058745
  simp only [CollatzResearch.WordTrace]
  refine ⟨75088598926525945498353689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50059065951017296998902459 75088598926525945498353689)
  ·
    refine ⟨56316449194894459123765267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75088598926525945498353689 56316449194894459123765267)
    ·
      refine ⟨84474673792341688685647901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56316449194894459123765267 84474673792341688685647901)
      ·
        refine ⟨31678002672128133257117963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84474673792341688685647901 31678002672128133257117963)
        ·
          refine ⟨47517004008192199885676945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31678002672128133257117963 47517004008192199885676945)
          ·
            refine ⟨35637753006144149914257709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47517004008192199885676945 35637753006144149914257709)
            ·
              refine ⟨13364157377304056217846641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35637753006144149914257709 13364157377304056217846641)
              ·
                refine ⟨10023118032978042163384981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13364157377304056217846641 10023118032978042163384981)
                ·
                  refine ⟨469833657795845726408671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10023118032978042163384981 469833657795845726408671)
                  ·
                    rfl

theorem cell21_2058745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_2058745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058745 prefixEnd_2058745 := by exact prefixLift 2058745
  have htrace : WordTrace (prefixWord ++ tailWord_2058745) baseStart_2058745 baseEnd_2058745 := by
    simpa [prefixWord, tailWord_2058745, baseEnd_2058745] using wordTrace_append hprefix tailTrace_2058745
  have hstable : (prefixWord ++ tailWord_2058745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058745).length < 2 ^ (prefixWord ++ tailWord_2058745).sum := by decide
  have hdescent : baseEnd_2058745 < baseStart_2058745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058762 : List Nat := [3, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_2058762 : Nat := 118140960795 + 2058762 * 2 ^ 59
def prefixEnd_2058762 : Nat := 4983230072969 + 3 ^ 40 * 2058762 * 2
def baseEnd_2058762 : Nat := 469837537427457474625303

theorem tailTrace_2058762 : CollatzResearch.WordTrace tailWord_2058762 prefixEnd_2058762 469837537427457474625303 := by
  unfold tailWord_2058762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18772304741866089350430635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50059479311642904934481693 18772304741866089350430635)
  ·
    refine ⟨28158457112799134025645953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18772304741866089350430635 28158457112799134025645953)
    ·
      refine ⟨21118842834599350519234465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28158457112799134025645953 21118842834599350519234465)
      ·
        refine ⟨15839132125949512889425849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21118842834599350519234465 15839132125949512889425849)
        ·
          refine ⟨11879349094462134667069387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15839132125949512889425849 11879349094462134667069387)
          ·
            refine ⟨17819023641693202000604081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11879349094462134667069387 17819023641693202000604081)
            ·
              refine ⟨13364267731269901500453061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17819023641693202000604081 13364267731269901500453061)
              ·
                refine ⟨2505800199613106531334949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13364267731269901500453061 2505800199613106531334949)
                ·
                  refine ⟨469837537427457474625303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2505800199613106531334949 469837537427457474625303)
                  ·
                    rfl

theorem cell21_2058762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_2058762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058762 prefixEnd_2058762 := by exact prefixLift 2058762
  have htrace : WordTrace (prefixWord ++ tailWord_2058762) baseStart_2058762 baseEnd_2058762 := by
    simpa [prefixWord, tailWord_2058762, baseEnd_2058762] using wordTrace_append hprefix tailTrace_2058762
  have hstable : (prefixWord ++ tailWord_2058762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058762).length < 2 ^ (prefixWord ++ tailWord_2058762).sum := by decide
  have hdescent : baseEnd_2058762 < baseStart_2058762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058776 : List Nat := [2, 1, 2, 3, 3, 1, 1, 8]
def baseStart_2058776 : Nat := 118140960795 + 2058776 * 2 ^ 59
def prefixEnd_2058776 : Nat := 4983230072969 + 3 ^ 40 * 2058776 * 2
def baseEnd_2058776 : Nat := 156613577472732187130647

theorem tailTrace_2058776 : CollatzResearch.WordTrace tailWord_2058776 prefixEnd_2058776 156613577472732187130647 := by
  unfold tailWord_2058776
  simp only [CollatzResearch.WordTrace]
  refine ⟨37544864794706818896366091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50059819726275758528488121 37544864794706818896366091)
  ·
    refine ⟨56317297192060228344549137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37544864794706818896366091 56317297192060228344549137)
    ·
      refine ⟨42237972894045171258411853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56317297192060228344549137 42237972894045171258411853)
      ·
        refine ⟨15839239835266939221904445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42237972894045171258411853 15839239835266939221904445)
        ·
          refine ⟨5939714938225102208214167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15839239835266939221904445 5939714938225102208214167)
          ·
            refine ⟨8909572407337653312321251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5939714938225102208214167 8909572407337653312321251)
            ·
              refine ⟨13364358611006479968481877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8909572407337653312321251 13364358611006479968481877)
              ·
                refine ⟨156613577472732187130647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13364358611006479968481877 156613577472732187130647)
                ·
                  rfl

theorem cell21_2058776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_2058776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058776 prefixEnd_2058776 := by exact prefixLift 2058776
  have htrace : WordTrace (prefixWord ++ tailWord_2058776) baseStart_2058776 baseEnd_2058776 := by
    simpa [prefixWord, tailWord_2058776, baseEnd_2058776] using wordTrace_append hprefix tailTrace_2058776
  have hstable : (prefixWord ++ tailWord_2058776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058776).length < 2 ^ (prefixWord ++ tailWord_2058776).sum := by decide
  have hdescent : baseEnd_2058776 < baseStart_2058776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058869 : List Nat := [1, 3, 4, 2, 2, 1, 8]
def baseStart_2058869 : Nat := 118140960795 + 2058869 * 2 ^ 59
def prefixEnd_2058869 : Nat := 4983230072969 + 3 ^ 40 * 2058869 * 2
def baseEnd_2058869 : Nat := 52206884031694340704639

theorem tailTrace_2058869 : CollatzResearch.WordTrace tailWord_2058869 prefixEnd_2058869 52206884031694340704639 := by
  unfold tailWord_2058869
  simp only [CollatzResearch.WordTrace]
  refine ⟨75093121578076714675867661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50062081052051143117245107 75093121578076714675867661)
  ·
    refine ⟨28159920591778768003450373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75093121578076714675867661 28159920591778768003450373)
    ·
      refine ⟨5279985110958519000646945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28159920591778768003450373 5279985110958519000646945)
      ·
        refine ⟨3959988833218889250485209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5279985110958519000646945 3959988833218889250485209)
        ·
          refine ⟨2969991624914166937863907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3959988833218889250485209 2969991624914166937863907)
          ·
            refine ⟨4454987437371250406795861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969991624914166937863907 4454987437371250406795861)
            ·
              refine ⟨52206884031694340704639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4454987437371250406795861 52206884031694340704639)
              ·
                rfl

theorem cell21_2058869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 8].length) (baseStart_2058869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058869 prefixEnd_2058869 := by exact prefixLift 2058869
  have htrace : WordTrace (prefixWord ++ tailWord_2058869) baseStart_2058869 baseEnd_2058869 := by
    simpa [prefixWord, tailWord_2058869, baseEnd_2058869] using wordTrace_append hprefix tailTrace_2058869
  have hstable : (prefixWord ++ tailWord_2058869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058869).length < 2 ^ (prefixWord ++ tailWord_2058869).sum := by decide
  have hdescent : baseEnd_2058869 < baseStart_2058869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058900 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2058900 : Nat := 118140960795 + 2058900 * 2 ^ 59
def prefixEnd_2058900 : Nat := 4983230072969 + 3 ^ 40 * 2058900 * 2
def baseEnd_2058900 : Nat := 469869030907599901325021

theorem tailTrace_2058900 : CollatzResearch.WordTrace tailWord_2058900 prefixEnd_2058900 469869030907599901325021 := by
  unfold tailWord_2058900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37547126120482203485123077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50062834827309604646830769 37547126120482203485123077)
  ·
    refine ⟨7040086147590413153460577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37547126120482203485123077 7040086147590413153460577)
    ·
      refine ⟨5280064610692809865095433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7040086147590413153460577 5280064610692809865095433)
      ·
        refine ⟨3960048458019607398821575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5280064610692809865095433 3960048458019607398821575)
        ·
          refine ⟨5940072687029411098232363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960048458019607398821575 5940072687029411098232363)
          ·
            refine ⟨8910109030544116647348545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5940072687029411098232363 8910109030544116647348545)
            ·
              refine ⟨6682581772908087485511409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8910109030544116647348545 6682581772908087485511409)
              ·
                refine ⟨5011936329681065614133557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6682581772908087485511409 5011936329681065614133557)
                ·
                  refine ⟨469869030907599901325021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5011936329681065614133557 469869030907599901325021)
                  ·
                    rfl

theorem cell21_2058900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2058900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058900 prefixEnd_2058900 := by exact prefixLift 2058900
  have htrace : WordTrace (prefixWord ++ tailWord_2058900) baseStart_2058900 baseEnd_2058900 := by
    simpa [prefixWord, tailWord_2058900, baseEnd_2058900] using wordTrace_append hprefix tailTrace_2058900
  have hstable : (prefixWord ++ tailWord_2058900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058900).length < 2 ^ (prefixWord ++ tailWord_2058900).sum := by decide
  have hdescent : baseEnd_2058900 < baseStart_2058900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058934 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2058934 : Nat := 118140960795 + 2058934 * 2 ^ 59
def prefixEnd_2058934 : Nat := 4983230072969 + 3 ^ 40 * 2058934 * 2
def baseEnd_2058934 : Nat := 469876790170823397758285

theorem tailTrace_2058934 : CollatzResearch.WordTrace tailWord_2058934 prefixEnd_2058934 469876790170823397758285 := by
  unfold tailWord_2058934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4693468270177576923561491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50063661548560820517989237 4693468270177576923561491)
  ·
    refine ⟨7040202405266365385342237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4693468270177576923561491 7040202405266365385342237)
    ·
      refine ⟨2640075901974887019503339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7040202405266365385342237 2640075901974887019503339)
      ·
        refine ⟨3960113852962330529255009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640075901974887019503339 3960113852962330529255009)
        ·
          refine ⟨2970085389721747896941257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3960113852962330529255009 2970085389721747896941257)
          ·
            refine ⟨2227564042291310922705943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970085389721747896941257 2227564042291310922705943)
            ·
              refine ⟨3341346063436966384058915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227564042291310922705943 3341346063436966384058915)
              ·
                refine ⟨5012019095155449576088373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341346063436966384058915 5012019095155449576088373)
                ·
                  refine ⟨469876790170823397758285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5012019095155449576088373 469876790170823397758285)
                  ·
                    rfl

theorem cell21_2058934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2058934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058934 prefixEnd_2058934 := by exact prefixLift 2058934
  have htrace : WordTrace (prefixWord ++ tailWord_2058934) baseStart_2058934 baseEnd_2058934 := by
    simpa [prefixWord, tailWord_2058934, baseEnd_2058934] using wordTrace_append hprefix tailTrace_2058934
  have hstable : (prefixWord ++ tailWord_2058934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058934).length < 2 ^ (prefixWord ++ tailWord_2058934).sum := by decide
  have hdescent : baseEnd_2058934 < baseStart_2058934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058948 : List Nat := [2, 3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2058948 : Nat := 118140960795 + 2058948 * 2 ^ 59
def prefixEnd_2058948 : Nat := 4983230072969 + 3 ^ 40 * 2058948 * 2
def baseEnd_2058948 : Nat := 469879985161562484524923

theorem tailTrace_2058948 : CollatzResearch.WordTrace tailWord_2058948 prefixEnd_2058948 469879985161562484524923 := by
  unfold tailWord_2058948
  simp only [CollatzResearch.WordTrace]
  refine ⟨37548001472395255583996749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50064001963193674111995665 37548001472395255583996749)
  ·
    refine ⟨14080500552148220843998781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37548001472395255583996749 14080500552148220843998781)
    ·
      refine ⟨5280187707055582816499543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14080500552148220843998781 5280187707055582816499543)
      ·
        refine ⟨7920281560583374224749315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280187707055582816499543 7920281560583374224749315)
        ·
          refine ⟨11880422340875061337123973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7920281560583374224749315 11880422340875061337123973)
          ·
            refine ⟨2227579188914074000710745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11880422340875061337123973 2227579188914074000710745)
            ·
              refine ⟨1670684391685555500533059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227579188914074000710745 1670684391685555500533059)
              ·
                refine ⟨2506026587528333250799589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670684391685555500533059 2506026587528333250799589)
                ·
                  refine ⟨469879985161562484524923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2506026587528333250799589 469879985161562484524923)
                  ·
                    rfl

theorem cell21_2058948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2058948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058948 prefixEnd_2058948 := by exact prefixLift 2058948
  have htrace : WordTrace (prefixWord ++ tailWord_2058948) baseStart_2058948 baseEnd_2058948 := by
    simpa [prefixWord, tailWord_2058948, baseEnd_2058948] using wordTrace_append hprefix tailTrace_2058948
  have hstable : (prefixWord ++ tailWord_2058948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058948).length < 2 ^ (prefixWord ++ tailWord_2058948).sum := by decide
  have hdescent : baseEnd_2058948 < baseStart_2058948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058990 : List Nat := [4, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_2058990 : Nat := 118140960795 + 2058990 * 2 ^ 59
def prefixEnd_2058990 : Nat := 4983230072969 + 3 ^ 40 * 2058990 * 2
def baseEnd_2058990 : Nat := 469889570133779744824837

theorem tailTrace_2058990 : CollatzResearch.WordTrace tailWord_2058990 prefixEnd_2058990 469889570133779744824837 := by
  unfold tailWord_2058990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9387191851329794042627803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50065023207092234894014949 9387191851329794042627803)
  ·
    refine ⟨14080787776994691063941705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9387191851329794042627803 14080787776994691063941705)
    ·
      refine ⟨10560590832746018297956279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14080787776994691063941705 10560590832746018297956279)
      ·
        refine ⟨15840886249119027446934419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10560590832746018297956279 15840886249119027446934419)
        ·
          refine ⟨23761329373678541170401629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15840886249119027446934419 23761329373678541170401629)
          ·
            refine ⟨8910498515129452938900611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23761329373678541170401629 8910498515129452938900611)
            ·
              refine ⟨13365747772694179408350917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8910498515129452938900611 13365747772694179408350917)
              ·
                refine ⟨2506077707380158639065797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13365747772694179408350917 2506077707380158639065797)
                ·
                  refine ⟨469889570133779744824837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2506077707380158639065797 469889570133779744824837)
                  ·
                    rfl

theorem cell21_2058990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_2058990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058990 prefixEnd_2058990 := by exact prefixLift 2058990
  have htrace : WordTrace (prefixWord ++ tailWord_2058990) baseStart_2058990 baseEnd_2058990 := by
    simpa [prefixWord, tailWord_2058990, baseEnd_2058990] using wordTrace_append hprefix tailTrace_2058990
  have hstable : (prefixWord ++ tailWord_2058990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058990).length < 2 ^ (prefixWord ++ tailWord_2058990).sum := by decide
  have hdescent : baseEnd_2058990 < baseStart_2058990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2058996 : List Nat := [2, 6, 1, 1, 3, 1, 1, 6]
def baseStart_2058996 : Nat := 118140960795 + 2058996 * 2 ^ 59
def prefixEnd_2058996 : Nat := 4983230072969 + 3 ^ 40 * 2058996 * 2
def baseEnd_2058996 : Nat := 156630313138508355908275

theorem tailTrace_2058996 : CollatzResearch.WordTrace tailWord_2058996 prefixEnd_2058996 156630313138508355908275 := by
  unfold tailWord_2058996
  simp only [CollatzResearch.WordTrace]
  refine ⟨37548876824308307682870421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50065169099077743577160561 37548876824308307682870421)
  ·
    refine ⟨1760103601139451922634551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37548876824308307682870421 1760103601139451922634551)
    ·
      refine ⟨2640155401709177883951827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760103601139451922634551 2640155401709177883951827)
      ·
        refine ⟨3960233102563766825927741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640155401709177883951827 3960233102563766825927741)
        ·
          refine ⟨1485087413461412559722903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3960233102563766825927741 1485087413461412559722903)
          ·
            refine ⟨2227631120192118839584355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485087413461412559722903 2227631120192118839584355)
            ·
              refine ⟨3341446680288178259376533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227631120192118839584355 3341446680288178259376533)
              ·
                refine ⟨156630313138508355908275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3341446680288178259376533 156630313138508355908275)
                ·
                  rfl

theorem cell21_2058996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_2058996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2058996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2058996 prefixEnd_2058996 := by exact prefixLift 2058996
  have htrace : WordTrace (prefixWord ++ tailWord_2058996) baseStart_2058996 baseEnd_2058996 := by
    simpa [prefixWord, tailWord_2058996, baseEnd_2058996] using wordTrace_append hprefix tailTrace_2058996
  have hstable : (prefixWord ++ tailWord_2058996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2058996).length < 2 ^ (prefixWord ++ tailWord_2058996).sum := by decide
  have hdescent : baseEnd_2058996 < baseStart_2058996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2058996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059004 : List Nat := [2, 2, 2, 1, 3, 2, 3, 6]
def baseStart_2059004 : Nat := 118140960795 + 2059004 * 2 ^ 59
def prefixEnd_2059004 : Nat := 4983230072969 + 3 ^ 40 * 2059004 * 2
def baseEnd_2059004 : Nat := 156630921708172943863825

theorem tailTrace_2059004 : CollatzResearch.WordTrace tailWord_2059004 prefixEnd_2059004 156630921708172943863825 := by
  unfold tailWord_2059004
  simp only [CollatzResearch.WordTrace]
  refine ⟨37549022716293816366016033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50065363621725088488021377 37549022716293816366016033)
  ·
    refine ⟨28161767037220362274512025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37549022716293816366016033 28161767037220362274512025)
    ·
      refine ⟨21121325277915271705884019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28161767037220362274512025 21121325277915271705884019)
      ·
        refine ⟨31681987916872907558826029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21121325277915271705884019 31681987916872907558826029)
        ·
          refine ⟨11880745468827340334559761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31681987916872907558826029 11880745468827340334559761)
          ·
            refine ⟨8910559101620505250919821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11880745468827340334559761 8910559101620505250919821)
            ·
              refine ⟨3341459663107689469094933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8910559101620505250919821 3341459663107689469094933)
              ·
                refine ⟨156630921708172943863825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3341459663107689469094933 156630921708172943863825)
                ·
                  rfl

theorem cell21_2059004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_2059004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059004 prefixEnd_2059004 := by exact prefixLift 2059004
  have htrace : WordTrace (prefixWord ++ tailWord_2059004) baseStart_2059004 baseEnd_2059004 := by
    simpa [prefixWord, tailWord_2059004, baseEnd_2059004] using wordTrace_append hprefix tailTrace_2059004
  have hstable : (prefixWord ++ tailWord_2059004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059004).length < 2 ^ (prefixWord ++ tailWord_2059004).sum := by decide
  have hdescent : baseEnd_2059004 < baseStart_2059004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
